import click
import requests
from sqlmodel import select
from sprint.scripts.common import ensure_session_exists
from sprint.tgi.db.database import get_session
from sprint.tgi.models import AbstractPatch

API_URL = "http://localhost:8001"

@click.group()
def synthesis():
    """
    CLI command to convert patches to JSON format.
    """
    pass

@synthesis.command("generate-patches")
@click.option('--version', required=True, help='Abstract patch version.')
@click.option('--session-id', required=True, help='Session id input.')
@click.option('--bid', required=False, help='If provided, only generate patch for this bug id.')
@click.option('--model', default='llama3.1:8b', help='Model name to use.')
@click.option('--max-trials', default=3, help='Maximum number of trials for generating patch.')
def generate_patches(version, session_id, bid, model, max_trials):
    """
    Generate concrete patches from abstract patches using the FastAPI endpoint.
    """
    # Ensure the session exists
    ensure_session_exists(session_id)

    with next(get_session()) as session:
        query = select(AbstractPatch).where(AbstractPatch.version == version)
        query = query.where(AbstractPatch.rewritten_source.isnot(None))
        if bid:
            query = query.where(AbstractPatch.bug_id == bid)
        patches = session.exec(query).all()
        if not patches:
            click.echo("No abstract patches found for the given parameters.")
            return

        for abs_patch in patches:
            payload = {
                "abstract_patch_id": abs_patch.id,
                "session_id": session_id,
                "model": model,
                "max_trials": max_trials,
                "previous_attempt_id": None
            }
            url = f"{API_URL}/generate_patches/{abs_patch.bug_id}"
            try:
                resp = requests.post(url, json=payload)
                if resp.status_code == 200:
                    result = resp.json()
                    click.echo(f"Generated patch for abstract patch id {abs_patch.id}: {result.get('id', result)}")
                else:
                    click.echo(f"Failed for abstract patch id {abs_patch.id}: {resp.text}")
            except Exception as e:
                click.echo(f"Error for abstract patch id {abs_patch.id}: {e}")

