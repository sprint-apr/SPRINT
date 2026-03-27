import click
from pathlib import Path
from sqlmodel import select
from sprint.scripts.batch import batch
from sprint.scripts.figure import figure
from sprint.scripts.sequential import sequential
from sprint.scripts.synthesis import synthesis
from sprint.scripts.tokens import tokens
from sprint.tgi.db.database import get_session
from sprint.tgi.models import ExperimentSession
from sprint.scripts.convert_to_concrete import convert
from sprint.scripts.register_abstract_patches import register_abstract_patches
from sprint.scripts.export_sprint_format import export_sprint_format

@click.group()
def cli():
    pass


@cli.command()
@click.option(
    "--session_id",
    type=str,
    required=True,
    help="Session ID to initialize."
)
@click.option(
    "--model",
    type=str,
    required=True,
    help="LLM model name to use (e.g. gpt-4.1, gpt-4.1-mini)."
)
def initialize_session(session_id: str, model: str):
    """
    Initialize a new experiment session.
    """
    with next(get_session()) as session:
        if session.exec(select(ExperimentSession).where(ExperimentSession.id == session_id)).first():
            click.echo(f"Session ID {session_id} already exists.")
            return

        new_session = ExperimentSession(id=session_id, model=model)
        session.add(new_session)
        session.commit()
        click.echo(f"Session {session_id} initialized successfully.")

@cli.command()
def list_sessions():
    """
    List all experiment sessions.
    """
    with next(get_session()) as session:
        sessions = session.exec(select(ExperimentSession)).all()
        if not sessions:
            click.echo("No sessions found.")
            return

        click.echo("Experiment Sessions:")
        for s in sessions:
            click.echo(f"- {s.id}")


cli.add_command(convert)
cli.add_command(sequential)
cli.add_command(synthesis)
cli.add_command(batch)
cli.add_command(register_abstract_patches)
cli.add_command(tokens)
cli.add_command(figure)
cli.add_command(export_sprint_format)

if __name__ == "__main__":
    cli()