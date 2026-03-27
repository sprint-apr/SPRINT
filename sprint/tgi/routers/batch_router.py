import random
from fastapi import APIRouter, HTTPException
from sqlmodel import select
from sprint.tgi import prompts
from sprint.tgi.config_box import OPENAI_BATCH_REQUESTS_DIR
from sprint.tgi.models import (
    AbstractPatch as AbstractPatchDB,
    BatchRequest,
    BatchRequestItem,
    ConcretePatch,
    ExperimentSession,
    TokenReference,
)
from sprint.tgi.data import AbstractPatch, Bug
from sprint.tgi.dependencies import SessionDep, BugsDep, OpenAIClientDep
import json

router = APIRouter(prefix="/batch", tags=["batch"])

@router.post("/cancel-all-running")
async def cancel_all_running_batches(openai_client: OpenAIClientDep):
    """
    Cancel all currently running (non-completed) OpenAI batch jobs.
    """
    # fetch all batch jobs
    batches = list(openai_client.batches.list().data)

    # filter only running or pending batches
    running_batches = [b for b in batches if b.status in {"validating", "in_progress", "finalizing", "cancelling", "finalizing"}]

    cancelled = []
    failed_to_cancel = []

    for batch in running_batches:
        try:
            openai_client.batches.cancel(batch.id)
            cancelled.append(batch.id)
        except Exception as e:
            failed_to_cancel.append({"id": batch.id, "error": str(e)})

    return {
        "cancelled": cancelled,
        "failed_to_cancel": failed_to_cancel,
        "total_cancelled": len(cancelled),
        "still_running": len(running_batches) - len(cancelled),
    }



@router.post("/register")
async def register_batch_requests(
    session_id: str,
    bugs: BugsDep,
    session: SessionDep,
    openai_client: OpenAIClientDep,
    bug_id: str | None = None,
):
    """
    Register batch requests for a given session ID.
    """
    bugs: list[Bug] = bugs.values() if not bug_id else [bugs[bug_id]]

    experiment_session = session.exec(
        select(ExperimentSession).where(ExperimentSession.id == session_id)
    ).first()

    if not experiment_session:
        raise HTTPException(status_code=404, detail="Experiment session not found.")

    batch_request_items = []
    for bug in bugs:
        abstract_patches = session.exec(
            select(AbstractPatchDB).where(
                (AbstractPatchDB.bug_id == bug.id)
                & (AbstractPatchDB.version == experiment_session.ap_version)
                & (AbstractPatchDB.rewritten_source.isnot(None))
            )
        ).all()

        batch_request_items.extend(
            BatchRequestItem(
                custom_id=f"{session_id}_{bug.id}_{patch.id}",
                session_id=session_id,
                bug_id=bug.id,
                patch_id=patch.id,
                messages=prompts.construct_openai_messages(
                    bug, AbstractPatch.from_db(patch)
                ),
            )
            for patch in abstract_patches
        )
        session.add_all(batch_request_items)

    # Split items into chunks of 1600 and create JSONL files
    size = 800
    for i in range(0, len(batch_request_items), size):
        items: list[BatchRequestItem] = batch_request_items[i : i + size]
        file_name = f"{session_id}_batch_{i // size + 1}.jsonl"
        file_path = OPENAI_BATCH_REQUESTS_DIR / file_name

        json_lines = [
            {
                "custom_id": f"{session_id}_{item.bug_id}_{item.patch_id}",
                "method": "POST",
                "url": "/v1/chat/completions",
                "body": {
                    "model": experiment_session.model,
                    "messages": item.messages,
                    "stream": False,
                },
            }
            for item in items
        ]

        with open(file_path, "w") as f:
            for line in json_lines:
                f.write(json.dumps(line) + "\n")
        upload_openai_files([file_path], openai_client)

        session.add(
            BatchRequest(
                session_id=session_id,
                file_path=str(file_path),
            )
        )

    session.commit()

    return


async def _register_batch_result_by_id(batch_id: str, session: SessionDep, openai_client: OpenAIClientDep):
    """
    Retrieve batch results for a given batch ID.
    """
    batch = openai_client.batches.retrieve(batch_id)
    if (batch.status != 'completed'):
        raise HTTPException(status_code=400, detail="Batch request is not completed.")

    output_file = openai_client.files.retrieve(batch.output_file_id)
    result_file_content = openai_client.files.content(output_file.id)
    if not (session_id := batch.metadata.get("session_id")):
        raise HTTPException(status_code=400, detail="Batch request does not contain session_id in metadata.")

    registered_patches = []
    for line in result_file_content.read().decode("utf-8").splitlines():
        try:
            data = json.loads(line)

            custom_id = data.get("custom_id")

            batch_item = session.exec(
                select(BatchRequestItem).where(BatchRequestItem.custom_id == custom_id)
            ).first()
            if not batch_item:
                raise HTTPException(
                    status_code=404, detail=f"Batch item with custom_id {custom_id} not found."
                )

            abstract_patch = session.exec(
                select(AbstractPatchDB).where(AbstractPatchDB.id == batch_item.patch_id)
            ).first()
            if not abstract_patch:
                raise HTTPException(
                    status_code=404, detail=f"AbstractPatch with ID {batch_item.patch_id} not found."
                )

            # 5. parse response content
            data = data['response']['body']
            patch_text = data['choices'][0]['message']['content']
            usage = data['usage']

            # 6. create ConcretePatch
            concrete_patch = ConcretePatch(
                abstract_patch_id=abstract_patch.id,
                trial=1,
                previous_attempt_id=None,
                valid_inference=is_valid_inference(patch_text),
                propmt_eval_count=usage["prompt_tokens"],
                eval_count=usage["completion_tokens"],
                patch=patch_text,
                session_id=session_id,
            )

            session.add(concrete_patch)
            registered_patches.append(concrete_patch)

        except Exception as e:
            continue  # ignore lines with errors

    session.commit()

    return {
        "batch_id": batch_id,
        "registered": [patch.id for patch in registered_patches],
        "count": len(registered_patches),
    }

@router.get("/{batch_id}/results")
async def register_batch_results(batch_id: str, session: SessionDep, openai_client: OpenAIClientDep):
    registered_patches = await _register_batch_result_by_id(batch_id, session, openai_client)
    return {
        "batch_id": batch_id,
        "registered": [patch.id for patch in registered_patches],
        "count": len(registered_patches),
    }

@router.post("/session/{session_id}/register-results")
async def register_all_results_for_session(session_id: str, session: SessionDep, openai_client: OpenAIClientDep):
    batch_requests = session.exec(
        select(BatchRequest).where(BatchRequest.session_id == session_id)
    ).all()

    total_registered = 0
    total_batches = 0
    failed_batches = []
    all_patch_ids = []

    for batch in batch_requests:
        if not batch.submitted_batch_id:
            continue

        try:
            registered = await _register_batch_result_by_id(batch.submitted_batch_id, session, openai_client)
            total_batches += 1
            total_registered += registered['count']
            all_patch_ids.extend(registered['registered'])
        except Exception as e:
            failed_batches.append({"batch_id": batch.id, "error": str(e)})

    return {
        "session_id": session_id,
        "total_batches_processed": total_batches,
        "total_registered_patches": total_registered,
        "registered_patch_ids": all_patch_ids,
        "failed_batches": failed_batches,
    }



@router.post("/{batch_id}/run")
async def run_batch_tasks(batch_id: str, session: SessionDep):
    """
    Run batch tasks for a given batch ID.
    """
    batch_request = session.exec(
        select(BatchRequest).where(BatchRequest.id == batch_id)
    ).first()

    if not batch_request:
        raise HTTPException(status_code=404, detail="Batch request not found.")

    # Simulate running batch tasks (replace with actual logic)
    for item in batch_request.items:
        item.result = {"status": "completed", "data": f"Processed {item.custom_id}"}

    session.commit()
    return {"batch_id": batch_id, "status": "Batch tasks completed"}


@router.post("/create")
async def create_batch_requests(
    session_id: str,
    bugs: BugsDep,
    session: SessionDep,
    d4j_version: str | None = None,
):
    experiment_session = session.exec(
        select(ExperimentSession).where(ExperimentSession.id == session_id)
    ).first()

    if not experiment_session:
        raise HTTPException(status_code=404, detail="Experiment session not found.")

    abstract_patches = session.exec(
        select(AbstractPatchDB).where(
            (AbstractPatchDB.version == experiment_session.ap_version)
            & (AbstractPatchDB.rewritten_source.isnot(None))
        )
    ).all()

    token_refs = session.exec(select(TokenReference)).all()
    token_ref_map = {ref.abstract_patch_id: ref for ref in token_refs}
    random.shuffle(abstract_patches)

    current_batch = []
    batches : list[list[BatchRequestItem]] = [current_batch]
    cumulative_tokens = 0
    for abstract_patch in abstract_patches:
        batch_request_item = BatchRequestItem(
            custom_id=f"{session_id}__{abstract_patch.bug_id}__{abstract_patch.id}",
            session_id=session_id,
            bug_id=abstract_patch.bug_id,
            patch_id=abstract_patch.id,
            messages=prompts.construct_openai_messages(
                bugs[abstract_patch.bug_id], AbstractPatch.from_db(abstract_patch)
            ),
        )

        ref = token_ref_map.get(abstract_patch.id)
        assert(ref is not None)
        estimated_tokens = ref.propmt_eval_count + max(ref.eval_count, 4000)

        cumulative_tokens += estimated_tokens
        if cumulative_tokens > 1000000:
            current_batch = []
            batches.append(current_batch)
            cumulative_tokens = 0

        current_batch.append(batch_request_item)
        cumulative_tokens += estimated_tokens

    for i, batch_items in enumerate(batches):
        session.add_all(batch_items)

        file_name = f"{session_id}_batch_{i + 1}.jsonl"
        file_path = OPENAI_BATCH_REQUESTS_DIR / file_name
        json_lines = [
            {
                "custom_id": item.custom_id,
                "method": "POST",
                "url": "/v1/chat/completions",
                "body": {
                    "model": experiment_session.model,
                    "messages": item.messages,
                    "stream": False,
                },
            }
            for item in batch_items
        ]

        with open(file_path, "w") as f:
            for line in json_lines:
                f.write(json.dumps(line) + "\n")

        # 3. save BatchRequest to DB
        session.add(
            BatchRequest(
                session_id=session_id,
                file_path=str(file_path),
                batch_index=i + 1,
            )
        )

    session.commit()
    return {
        "session_id": session_id,
        "batch_count": len(batches),
    }

@router.post("/batch-per-bug")
async def create_batch_per_bug(
    session_id: str,
    bugs: BugsDep,
    session: SessionDep,
):
    """
    Group AbstractPatches per bug and register BatchRequestItems in the DB only.
    """
    experiment_session = session.exec(
        select(ExperimentSession).where(ExperimentSession.id == session_id)
    ).first()
    if not experiment_session:
        raise HTTPException(status_code=404, detail="Experiment session not found.")

    total_batches = 0
    total_items = 0

    for batch_count, bug in enumerate(bugs.values()):
        abstract_patches = session.exec(
            select(AbstractPatchDB).where(
                (AbstractPatchDB.bug_id == bug.id)
                & (AbstractPatchDB.version == experiment_session.ap_version)
                & (AbstractPatchDB.rewritten_source.isnot(None))
            )
        ).all()

        if not abstract_patches:
            continue

        batch_items: list[BatchRequestItem] = []

        for abstract_patch in abstract_patches:
            messages = prompts.construct_openai_messages(
                bug, AbstractPatch.from_db(abstract_patch)
            )

            batch_items.append(
                BatchRequestItem(
                    custom_id=f"{session_id}__{bug.id}__{abstract_patch.id}",
                    session_id=session_id,
                    bug_id=bug.id,
                    patch_id=abstract_patch.id,
                    messages=messages,
                )
            )

        session.add_all(batch_items)
        total_batches += 1
        total_items += len(batch_items)

        # Create jsonl file
        file_name = f"{session_id}_{bug.id}.jsonl"
        file_path = OPENAI_BATCH_REQUESTS_DIR / file_name
        json_lines = [
            {
                "custom_id": item.custom_id,
                "method": "POST",
                "url": "/v1/chat/completions",
                "body": {
                    "model": experiment_session.model,
                    "messages": item.messages,
                    "stream": False,
                },
            }
            for item in batch_items
        ]
        with open(file_path, "w") as f:
            for line in json_lines:
                f.write(json.dumps(line) + "\n")

        # Register BatchRequest
        session.add(
            BatchRequest(
                session_id=session_id,
                file_path=str(file_path),
                batch_index=batch_count + 1,
            )
        )

    session.commit()
    return {
        "session_id": session_id,
        "total_batches": total_batches,
        "total_items": total_items,
    }
