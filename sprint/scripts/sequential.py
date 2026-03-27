from pathlib import Path
from time import sleep
from sqlalchemy.orm import sessionmaker
from sqlmodel import create_engine
from sprint.tgi.config_box import DATABASE_URL
from sprint.tgi.db.database import get_session
import datetime
from multiprocessing import Process, Queue
import click, logging
import openai
from sqlmodel import Session, select

from sprint.tgi.data import AbstractPatch as AbstractPatchData
from sprint.tgi.initializer import API_KEYS, get_or_initialize_bugs
from sprint.tgi.models import APIKeyUsage, AbstractPatch, Bug, ConcretePatch, ExperimentSession
from sprint.tgi.prompts import construct_openai_messages
from sprint.tgi.utils import is_valid_inference

# Shared logger setup (used by both main and worker processes)
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(processName)s] %(levelname)s: %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)

MODEL_GROUPS = {
    "gpt-4.1-cheap": ["gpt-4.1-mini", "gpt-4.1-nano"],
    "gpt-4.1": ["gpt-4.1"],
}

def model_group(model_name: str) -> str:
    for group, members in MODEL_GROUPS.items():
        if model_name in members:
            return group
    return model_name  # fallback

def get_all_models_in_group(group_name: str) -> list[str]:
    return MODEL_GROUPS.get(group_name, [group_name])

class TokenTracker:
    def __init__(self, db: Session, daily_limit: int):
        self.db = db
        self.daily_limit = daily_limit


    def get_usage(self, api_key: str, model: str) -> APIKeyUsage:
        today = datetime.datetime.now(datetime.timezone.utc).date()
        usage = self.db.exec(
            select(APIKeyUsage)
            .where(APIKeyUsage.api_key == api_key)
            .where(APIKeyUsage.model == model)
            .where(APIKeyUsage.date == today)
        ).first()
        if not usage:
            usage = APIKeyUsage(api_key=api_key, model=model, date=today)
            self.db.add(usage)
            self.db.commit()
            self.db.refresh(usage)
        return usage

    def remaining_tokens(self, api_key: str, model: str) -> int:
        """
        Return remaining token quota for this key today
        (calculated based on cumulative usage across the model group)
        """
        today = datetime.datetime.now(datetime.timezone.utc).date()
        model_group_name = model_group(model)
        all_model_names_in_group = get_all_models_in_group(model_group_name)

        result = self.db.exec(
            select(APIKeyUsage)
            .where(APIKeyUsage.api_key == api_key)
            .where(APIKeyUsage.model.in_(all_model_names_in_group))
            .where(APIKeyUsage.date == today)
        ).all()

        total_used = sum(r.input_tokens + r.output_tokens for r in result)
        return max(self.daily_limit - total_used, 0)



    def can_use(self, api_key: str, model: str) -> bool:
        today = datetime.datetime.now(datetime.timezone.utc).date()
        model_group_name = model_group(model)
        all_model_names_in_group = get_all_models_in_group(model_group_name)

        # Aggregate usage across all models in the group

        result = self.db.exec(
            select(APIKeyUsage)
            .where(APIKeyUsage.api_key == api_key)
            .where(APIKeyUsage.model.in_(all_model_names_in_group))
            .where(APIKeyUsage.date == today)
        ).all()

        total_in  = sum(r.input_tokens for r in result)
        total_out = sum(r.output_tokens for r in result)

        return (total_in + total_out) < self.daily_limit

    def record_usage(self, api_key: str, model: str ,in_tokens: int, out_tokens: int):
        usage = self.get_usage(api_key, model)
        usage.input_tokens  += in_tokens
        usage.output_tokens += out_tokens
        usage.last_updated   = datetime.datetime.now(datetime.timezone.utc)
        self.db.add(usage)
        self.db.commit()

    def seconds_until_utc_midnight(self, model: str) -> int:
        now = datetime.datetime.now(datetime.timezone.utc)
        if model == 'gpt-4.1':
            # gpt-4.1: wait until UTC midnight
            midnight = (now + datetime.timedelta(days=1)).replace(hour=0, minute=0, second=0, microsecond=0)
        else:
            # gpt-4.1-mini, gpt-4.1-nano: wait until UTC midnight + 1 hour
            midnight = (now + datetime.timedelta(days=1)).replace(hour=1, minute=0, second=0, microsecond=0)

        return int((midnight - now).total_seconds())

def infer_single(ap: AbstractPatch, bug: Bug, client: openai.OpenAI, session: ExperimentSession) -> ConcretePatch:
    """
    Call OpenAI and return token usage from response.usage.
    """
    messages = construct_openai_messages(bug, AbstractPatchData.from_db(ap))

    response = client.chat.completions.create(
        model=session.model,
        messages=messages,
    )

    # 3. Parse response JSON
    patch_text = response.choices[0].message.content
    usage      = response.usage
    in_toks    = usage.prompt_tokens
    out_toks   = usage.completion_tokens

    patch = ConcretePatch(
        abstract_patch_id=ap.id,
        trial=1,
        previous_attempt_id=None,
        valid_inference=is_valid_inference(patch_text),
        propmt_eval_count=in_toks,
        eval_count=out_toks,
        patch=patch_text,
        session_id=session.id,
    )

    return patch
 


@click.group()
def sequential():
    pass

def key_worker(api_key: str, task_q: Queue, result_q: Queue, session_id: str):
    """
    Each worker operates with its own API key.
    Waits until UTC midnight when token limit is exhausted, then retries.
    Commits to DB immediately upon completion and sends only AP id or error to result queue.
    """
    # imports are done inside the worker
    logger = logging.getLogger(f"worker-{api_key[:20]}")
    logger.info("Worker started, API key ready")

    engine = create_engine(
        DATABASE_URL,
        pool_pre_ping=True,      # ping before reusing connection
    )
    with Session(engine) as session:

        bugs    = get_or_initialize_bugs()
        exp = session.exec(
            select(ExperimentSession).where(ExperimentSession.id == session_id)
        ).first()
        daliy_limit = 2_400_000 if exp.model in ["gpt-4.1-mini", "gpt-4.1-nano"] else 240_000
        # daliy_limit = 2_400_000
        tracker = TokenTracker(session, daily_limit=daliy_limit)
        client = openai.OpenAI(api_key=api_key)
        model = exp.model

        while True:
            ap = task_q.get()
            if ap is None:
                break  # termination signal
            logger.info(f"Processing AP id={ap.id}")

            # Log remaining token quota
            remaining = tracker.remaining_tokens(api_key, model)
            logger.info(f"Remaining tokens (model={model}) for {api_key[:20]}...: {remaining} tokens")

            # Check token limit
            if not tracker.can_use(api_key, model):
                wait = tracker.seconds_until_utc_midnight(model)
                logger.warning(f"Key exhausted (model: {model})! Waiting {wait}s before retry")
                sleep(wait)

            # Actual call & immediate DB commit
            try:
                concrete: ConcretePatch = infer_single(
                    ap, bugs[ap.bug_id], client, exp
                )
                # save immediately inside worker
                session.add(concrete)
                session.commit()
                # Record token usage
                tracker.record_usage(
                    api_key,
                    model,
                    concrete.propmt_eval_count,
                    concrete.eval_count,
                )
                logger.info(f"Done AP id={ap.id} (in={concrete.propmt_eval_count}, out={concrete.eval_count} model={model})")


                # send AP id as success signal
                result_q.put((ap.id, None))
            except Exception as e:
                logger.error(f"Failed AP id={ap.id}: {e}", exc_info=True)

                result_q.put((ap.id, str(e)))

        # Notify worker done
        result_q.put((None, "DONE"))

def _infer(
    session_id: str,
    patches: list[AbstractPatch],
    keys: list[str],
    logger: logging.Logger,
):
    # done_subq = (
    #     select(ConcretePatch.abstract_patch_id)
    #     .where(ConcretePatch.session_id == session_id)
    # )

    logger.info(f"Total AP count: {len(patches)}")

    task_q = Queue()
    result_q = Queue()

    # Spawn one worker process per API key
    workers = []
    for api_key in keys:
        p = Process(
            target=key_worker,
            args=(api_key, task_q, result_q, session_id),
            name=f"worker-{api_key[:20]}",
        )
        p.start()
        workers.append(p)

    # Feed APs into task queue & send termination signals
    for ap in patches:
        task_q.put(ap)
    for _ in workers:
        task_q.put(None)

    # Monitor results: id or error, and worker DONE signals
    done_workers = 0
    while done_workers < len(workers):
        ap_id, err = result_q.get()
        if ap_id is None and err == "DONE":
            done_workers += 1
            logger.info(f"Worker done signal received ({done_workers}/{len(workers)})")

        elif err:
            logger.error(f"Error processing AP {ap_id}: {err}")

        else:
            logger.info(f"AP {ap_id} done")


    for p in workers:
        p.join()

    logger.info("All APs processed")

@sequential.command()
@click.argument("session_id")
@click.option("--limit", type=int, default=2_400_000)
@click.option("--bug-id", type=str, default=None, help="Only infer patches for a specific bug.")
def infer(session_id: str, limit: int, bug_id: str):
    log_dir = Path("logs_infer")
    log_dir.mkdir(exist_ok=True)
    log_path = log_dir / f"infer-{session_id}.log"
    file_handler = logging.FileHandler(log_path)
    file_handler.setFormatter(logging.Formatter("%(asctime)s [%(processName)s] %(levelname)s: %(message)s", datefmt="%Y-%m-%d %H:%M:%S"))
    logging.getLogger().addHandler(file_handler)

    logger = logging.getLogger("main")
    logger.info(f"Logging to {log_path}")
    logger.info(f"Starting session {session_id}")

    """One process per API key; each worker handles its own DB commits."""
    with next(get_session()) as session:
        done_subq = (
            select(ConcretePatch.abstract_patch_id)
            .where(ConcretePatch.session_id == session_id)
        )

        query = select(AbstractPatch).where(
            AbstractPatch.id.not_in(done_subq),
            AbstractPatch.pfl == True,
        )
        if bug_id:
            query = query.where(AbstractPatch.bug_id == bug_id)
        patches = session.exec(
            query.limit(limit)
        ).all()

        _infer(
            session_id,
            patches,
            keys=API_KEYS,
            logger=logger,
        )

@sequential.command()
@click.option("--model", type=str, default="gpt-4.1")
def baseline(model: str):
    logger = logging.getLogger("baseline")
    logger.info(f"Starting baseline session")

    if model != "gpt-4.1":
        session_ids = [
            f'baseline-{model}-{n}' for n in range(1, 11)
        ]
    else:
        session_ids = [
            f'baseline-{n}' for n in range(1, 11)
        ]

    with next(get_session()) as db:
        for sid in session_ids:
            logger.info(f"===== Starting session {sid} =====")

            exp = db.exec(
                select(ExperimentSession).where(ExperimentSession.id == sid)
            ).first()
            if not exp:
                exp = ExperimentSession(id=sid, model=model)
                db.add(exp)
                db.commit()
                db.refresh(exp)
                logger.info(f"Registered ExperimentSession: {sid} (model={model}")

            done_subq = (
                select(ConcretePatch.abstract_patch_id)
                .where(ConcretePatch.session_id == sid)
            )

            patches = db.exec(
                select(AbstractPatch).where(
                    AbstractPatch.fault_desc == "WrongExp",
                    AbstractPatch.rewriting_instr.op("~")(r"^sed '[0-9]+c\"<MASK>\""),
                    AbstractPatch.id.not_in(done_subq)
                )
            ).all()
            logger.info(f"Total AP count: {len(patches)}")
            _infer(
                sid,
                patches,
                keys=API_KEYS[:2],
                logger=logger,
            )


