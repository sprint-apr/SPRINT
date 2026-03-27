from datetime import datetime, timezone
import json
import time
import itertools
import click
from openai import OpenAI
from sqlmodel import select
from sprint.tgi.db.database import get_session
from sprint.tgi.initializer import get_or_initialize_bugs
from sprint.tgi.models import AbstractPatch, BatchRequest, ConcretePatch, ExperimentSession
from sprint.tgi.models import BatchRequestItem
from rich.console import Console
from rich.table import Table
from rich import box

from sprint.tgi.utils import is_valid_inference


API_KEYS = [
    'YOUR_OPENAI_API_KEY_HERE',
]
KEY_CYCLE = itertools.cycle(API_KEYS)
CHECK_INTERVAL_SECONDS = 30

executed_keys_today = set()

def get_today_key_id(api_key: str):
    now = datetime.now(timezone.utc)
    return f"{api_key[:20]}_{now.strftime('%Y-%m-%d')}"


def is_batch_running(client: OpenAI) -> bool:
    try:
        active_batches = client.batches.list(limit=20)
        return any(batch.status == "in_progress" for batch in active_batches.data)
    except Exception as e:
        click.echo(f"⚠️ Failed to check batch status: {e}")
        return True  # conservative fallback on failure

def get_custom_ids_from_batch_file(file_path: str) -> set[str]:
    custom_ids = set()
    with open(file_path, "r") as f:
        for line in f:
            data = json.loads(line)
            custom_ids.add(data["custom_id"])
    return custom_ids

@click.group()
def batch():
    """Collection of batch-related CLI commands."""
    pass


@batch.command()
def run_batches_free():
    """Sequentially execute pending batches (only when conditions are met)."""
    with next(get_session()) as session:
        pending_batches = session.exec(
            select(BatchRequest).where(BatchRequest.file_id.is_(None))
        ).all()

        if not pending_batches:
            click.echo("✅ No pending batches.")
            return

        click.echo(f"🔄 Batches to execute: {len(pending_batches)}")
        used_keys_today = set()
        key_to_client = {}

        for idx, batch in enumerate(pending_batches):
            key = next(KEY_CYCLE)
            # Find a key that hasn't been used today and can run a batch
            selected_key = None
            for key in API_KEYS:
                today_key_id = get_today_key_id(key)

                if today_key_id in used_keys_today:
                    continue

                if key not in key_to_client:
                    key_to_client[key] = OpenAI(api_key=key)

                client = key_to_client[key]
                if is_batch_running(client):
                    click.echo(f"⏭️ Key {key[:10]}... has a running batch. Skipping.")
                    continue

                selected_key = key
                break  # found a usable key

            if not selected_key:
                click.echo("⛔ All keys have been used today or are busy. Exiting.")
                break

            # Execute the batch
            client = key_to_client[selected_key]
            today_key_id = get_today_key_id(selected_key)

            if is_batch_running(client):
                click.echo(f"⏸️ API key {key[:10]}... has an active batch. Skipping.")
                continue

            click.echo(f" [{idx+1}/{len(pending_batches)}] 🔍 Creating batch {batch.id}... (API key: {key[:10]}...)")
            try:
                with open(batch.file_path, "rb") as f:
                    uploaded = client.files.create(file=f, purpose="batch")

                response = client.batches.create(
                    input_file_id=uploaded.id,
                    endpoint="/v1/chat/completions",
                    completion_window="24h",
                    metadata={
                        "session_id": batch.session_id,
                        "batch_index": str(batch.batch_index),
                        "batch_file_path": batch.file_path,
                    }
                )

                batch.file_id = uploaded.id
                batch.submitted_batch_id = response.id
                batch.api_key_used = key

                session.add(batch)
                session.commit()

                executed_keys_today.add(today_key)  # mark as used today
                click.echo(f"✅ Batch {batch.id} created (file_id={uploaded.id})")
                break  # only one batch per key per day

            except Exception as e:
                click.echo(f"❌ Batch {batch.id} failed: {e}")

        click.echo("🎉 All eligible batches for today have been executed.")


console = Console()

@batch.command()
@click.argument("session_id")
def run_loop(session_id: str):
    """Run pending batches one at a time. Start the next after the previous one completes."""
    client = OpenAI(api_key=API_KEYS[0])

    with next(get_session()) as session:
        while True:

            
            # 1. Check running batch
            try:
                active_batches = client.batches.list(limit=50)
                running = any(batch.status in ("in_progress", "finalizing") for batch in active_batches.data)
            except Exception as e:
                console.print(f"[red]Failed to check batch status:[/red] {e}")
                time.sleep(CHECK_INTERVAL_SECONDS)
                continue

            if running:
                console.print("[yellow]A batch is currently running. Waiting before next check...[/yellow]")
                time.sleep(CHECK_INTERVAL_SECONDS)
                continue

            # 2. Fetch pending batches
            pending_batches = session.exec(
                select(BatchRequest).where(
                    (BatchRequest.session_id == session_id) & (BatchRequest.file_id.is_(None))
                ).order_by(BatchRequest.batch_index)
            ).all()

            try:
                submitted_batches = session.exec(
                    select(BatchRequest).where(
                        (BatchRequest.session_id == session_id) & (BatchRequest.submitted_batch_id.is_not(None))
                    )
                ).all()

                submitted_batch_map = {b.submitted_batch_id: b for b in submitted_batches}
                openai_batches = client.batches.list(limit=100)

                for ob in openai_batches.data:
                    if ob.id in submitted_batch_map:
                        b = submitted_batch_map[ob.id]
                        if b.status != ob.status:  # update only on status change
                            b.status = ob.status
                            session.add(b)

                session.commit()

            except Exception as e:
                console.print(f"[red]⚠️ Failed to update submitted batch statuses: {e}[/red]")

            if not pending_batches:
                console.print("[green]No pending batches found. Exiting.[/green]")
                break

            # Display pending batch list
            table = Table(title=f"Pending Batches for Session {session_id}", box=box.SIMPLE)
            table.add_column("Batch Index", style="cyan", justify="right")
            table.add_column("Batch ID", style="magenta")
            table.add_column("File Path", style="white")

            for b in pending_batches:
                table.add_row(str(b.batch_index), str(b.id), b.file_path or "(no file)")

            console.print(table)

            next_batch = pending_batches[0]
            console.print(f"[bold blue]Launching Batch: {next_batch.id} (Index: {next_batch.batch_index})[/bold blue]")

            try:
                with open(next_batch.file_path, "rb") as f:
                    uploaded = client.files.create(file=f, purpose="batch")

                response = client.batches.create(
                    input_file_id=uploaded.id,
                    endpoint="/v1/chat/completions",
                    completion_window="24h",
                    metadata={
                        "session_id": next_batch.session_id,
                        "batch_index": str(next_batch.batch_index),
                        "batch_file_path": next_batch.file_path,
                    },
                )

                next_batch.file_id = uploaded.id
                next_batch.submitted_batch_id = response.id
                next_batch.submitted_at = datetime.utcnow()
                next_batch.status = response.status


                session.add(next_batch)
                session.commit()

                console.print(f"[green]✅ Batch submitted successfully: {next_batch.id}[/green]")
                console.print(f"  ↪ Submitted Batch ID: [bold]{response.id}[/bold]")

                # Table for batch submission summary
                result_table = Table(box=box.MINIMAL_DOUBLE_HEAD)
                result_table.add_column("Submitted Batch ID", style="bold green")
                result_table.add_column("Created", style="dim")
                result_table.add_column("Status", style="cyan")

                result_table.add_row(
                    response.id,
                    datetime.utcfromtimestamp(response.created_at).strftime("%Y-%m-%d %H:%M:%S"),
                    response.status,
                )

                console.print(result_table)

            except Exception as e:
                console.print(f"[red]❌ Failed to submit batch:[/red] {e}")

            time.sleep(5)


@batch.command()
@click.argument("session_id")
def recover_failed_batches(session_id: str):
    """
    Recover failed batches by individually re-processing items not yet registered as ConcretePatch.
    """
    client = OpenAI(api_key=API_KEYS[0])
    with next(get_session()) as session:
        click.echo(f"\n🔍 Looking for failed batches in session: {session_id}")

        # Get all failed batches (submitted but not completed)
        batch_reqs = session.exec(
            select(BatchRequest)
            .where(BatchRequest.session_id == session_id)
        ).all()

        failed_batches = []
        for b in batch_reqs:
            try:
                batch_status = client.batches.retrieve(b.submitted_batch_id)
                if batch_status.status != "completed":
                    failed_batches.append(b)
            except Exception:
                failed_batches.append(b)  # treat as failed if retrieval fails

        if not failed_batches:
            click.echo("✅ No failed batches found.")
            return

        # Count total unregistered items
        total_targets = 0
        recover_targets = []
        for batch in failed_batches:
            custom_ids = get_custom_ids_from_batch_file(batch.file_path)

            items = session.exec(
                select(BatchRequestItem).where(
                    (BatchRequestItem.session_id == session_id)
                    & (BatchRequestItem.custom_id.in_(custom_ids))
                )
            ).all()

            for item in items:
                existing = session.exec(
                    select(ConcretePatch).where(
                        (ConcretePatch.abstract_patch_id == item.patch_id)
                    )
                ).first()
                if not existing:
                    recover_targets.append((batch, item))

        total_targets = len(recover_targets)
        if total_targets == 0:
            click.echo("🟡 All items already recovered.")
            return

        click.echo(f"📦 {len(failed_batches)} failed batches found.")
        click.echo(f"🎯 {total_targets} BatchRequestItems require recovery.\n")

        # Load experiment session info
        experiment_session = session.exec(
            select(ExperimentSession).where(ExperimentSession.id == session_id)
        ).first()

        completed = 0
        skipped = 0

        for i, (batch, item) in enumerate(recover_targets):
            # Check again in case of race conditions
            existing = session.exec(
                select(ConcretePatch).where(
                    (ConcretePatch.abstract_patch_id == item.patch_id)
                )
            ).first()
            if existing:
                skipped += 1
                status = f"⏩ skipped"
            else:
                try:
                    response = client.chat.completions.create(
                        model=experiment_session.model,
                        messages=item.messages,
                    )
                    patch_text = response.choices[0].message.content
                    usage = response.usage

                    patch = ConcretePatch(
                        abstract_patch_id=item.patch_id,
                        trial=1,
                        previous_attempt_id=None,
                        valid_inference=is_valid_inference(patch_text),
                        propmt_eval_count=usage.prompt_tokens,
                        eval_count=usage.completion_tokens,
                        patch=patch_text,
                        session_id=session_id,
                    )
                    session.add(patch)
                    session.commit()
                    completed += 1
                    status = f"✅ recovered"
                except Exception as e:
                    session.rollback()
                    status = f"❌ failed ({type(e).__name__}: {e})"

            remaining = total_targets - (completed + skipped)
            click.echo(f"[{i+1}/{total_targets}] {status} — remaining: {remaining}")

        click.echo("\n🎉 Recovery complete.")
        click.echo(f"✅ recovered: {completed}")
        click.echo(f"⏩ skipped:  {skipped}")
        click.echo(f"🧮 total:    {total_targets}")

@batch.command()
@click.argument("session_id")
@click.option("--max-workers", default=5, help="Number of parallel inference workers (default: 5)")
def infer_ap_parallel(session_id: str, max_workers: int):
    """
    Run parallel inference on AbstractPatches and save ConcretePatch results (without BatchRequestItem).
    Bugs are loaded via get_or_initialize_bugs().
    """
    from concurrent.futures import ThreadPoolExecutor, as_completed
    from sprint.tgi.prompts import construct_openai_messages
    from sprint.tgi.data import AbstractPatch as AbstractPatchData
    from sprint.tgi.utils import is_valid_inference

    client = OpenAI(api_key=API_KEYS[0])

    with next(get_session()) as session:
        experiment_session = session.exec(
            select(ExperimentSession).where(ExperimentSession.id == session_id)
        ).first()
        if not experiment_session:
            click.echo(f"❌ ExperimentSession '{session_id}' not found.")
            return

        # Collect target APs (based on session version)
        abstract_patches = session.exec(
            select(AbstractPatch).where(
                (AbstractPatch.version == experiment_session.ap_version)
                & (AbstractPatch.rewritten_source.isnot(None))
            )
        ).all()

        if not abstract_patches:
            click.echo(f"🟡 No AbstractPatches for session '{session_id}'")
            return

        # Load bugs
        bugs = get_or_initialize_bugs()

        # Only target APs that don't yet have a ConcretePatch
        ap_targets = [
            ap for ap in abstract_patches
            if not session.exec(
                select(ConcretePatch).where(ConcretePatch.abstract_patch_id == ap.id)
            ).first()
        ]

        click.echo(f"🎯 Total {len(ap_targets)} APs targeted (excluding already processed)")
        if not ap_targets:
            click.echo("✅ All APs have already been processed.")
            return

        def infer_single(ap):
            bug = bugs.get(ap.bug_id)
            if not bug:
                return (ap.id, None, f"⚠️ Bug not found")

            try:
                messages = construct_openai_messages(bug, AbstractPatchData.from_db(ap))
                response = client.chat.completions.create(
                    model=experiment_session.model,
                    messages=messages,
                )
                patch_text = response.choices[0].message.content
                usage = response.usage

                concrete_patch = ConcretePatch(
                    abstract_patch_id=ap.id,
                    trial=1,
                    previous_attempt_id=None,
                    valid_inference=is_valid_inference(patch_text),
                    propmt_eval_count=usage.prompt_tokens,
                    eval_count=usage.completion_tokens,
                    patch=patch_text,
                    session_id=session_id,
                )
                return (ap.id, concrete_patch, None)
            except Exception as e:
                return (ap.id, None, f"{type(e).__name__}: {e}")

        completed = 0
        failed = 0
        results: list[ConcretePatch] = []
        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            future_to_apid = {
                executor.submit(infer_single, ap): ap.id
                for ap in ap_targets
            }

            for i, future in enumerate(as_completed(future_to_apid)):
                ap_id = future_to_apid[future]
                try:
                    ap_id, result, error = future.result()
                    if result:
                        results.append(result)
                        completed += 1
                        click.echo(f"[{i+1}/{len(ap_targets)}] ✅ {ap_id} done")
                    else:
                        failed += 1
                        click.echo(f"[{i+1}/{len(ap_targets)}] ❌ {ap_id} failed: {error}")
                except Exception as e:
                    failed += 1
                    click.echo(f"[{i+1}/{len(ap_targets)}] ❌ {ap_id} crashed: {e}")

        results.append(result)
        session.add_all(results)
        session.commit()
        click.echo("\n🎉 Parallel inference complete")
        click.echo(f"✅ Succeeded: {completed}")
        click.echo(f"❌ Failed: {failed}")
        click.echo(f"🧮 Total: {len(ap_targets)}")
