from collections import defaultdict
import json
import re
import click
import shutil
from dataclasses import dataclass
from pathlib import Path
from sqlmodel import and_, select
from sprint.tgi.db.database import get_session
from sprint.tgi.models import ConcretePatch, AbstractPatch, ExperimentSession

@click.group()
def convert():
    """
    CLI command to convert patches to JSON format.
    """
    pass

@dataclass
class Patch:
    source_path: str
    bug_id: str
    line_from: int
    line_to: int
    patch_code: str
    abstract_patch_id: int
    concrete_patch_id: int
    

def _write_concrete_patches(output_path: Path, session_id, session, bug_id=None):

    # Query ConcretePatch and join with AbstractPatch
    statement = select(ConcretePatch, AbstractPatch).join(
        AbstractPatch,
        and_(
            AbstractPatch.pfl == True,
            ConcretePatch.abstract_patch_id == AbstractPatch.id,
            ConcretePatch.session_id == session_id,
            ConcretePatch.valid_inference == True,
        )
    )
    if bug_id:
        statement = statement.where(AbstractPatch.bug_id == bug_id)

    if bug_id:
        # re-export for a specific bug only: overwrite that bug's file and keep the rest
        output_path.mkdir(parents=True, exist_ok=True)
    else:
        if (output_path.exists()):
            shutil.rmtree(output_path)
        output_path.mkdir(parents=True, exist_ok=False)

    patches = defaultdict(list)
    pattern = re.compile(r"<patch_code>(.*?)</patch_code>", re.DOTALL)

    for concrete_patch, abstract_patch in session.exec(statement).all():
        # Split the patch code by <patch_code>
        patch_segments = pattern.findall(concrete_patch.patch)
        for patch_code in patch_segments:
            if patch_code.strip():  # Ignore empty segments
                patch = Patch(
                    source_path=abstract_patch.file,
                    bug_id=abstract_patch.bug_id,
                    line_from=abstract_patch.line,
                    line_to=abstract_patch.line,
                    patch_code=abstract_patch.rewritten_source.replace("\"<MASK>\"", patch_code),
                    abstract_patch_id=abstract_patch.id,
                    concrete_patch_id=concrete_patch.id,
                )
                entry = patch.__dict__.copy()
                entry["prunned"] = abstract_patch.prunned
                entry["pfl"] = abstract_patch.pfl
                patches[abstract_patch.bug_id].append(entry)

    for bug_id, patch_list in patches.items():
        # Serialize to JSON
        bug_output_path = output_path / bug_id / "patches.json"
        bug_output_path.parent.mkdir(parents=True, exist_ok=True)
        with bug_output_path.open("w", encoding="utf-8") as f:
            json.dump(patch_list, f, indent=4)

@convert.command()
@click.option(
    "--output",
    type=click.Path(dir_okay=True, writable=True, path_type=Path),
    default="patches.json",
    help="Path to the output JSON file.",
    required=True
)
@click.option(
    "--session-id",
    type=str,
    help="Session ID to filter patches.",
    required=True
)
@click.option(
    "--bug-id",
    type=str,
    default=None,
    help="Only export patches for a specific bug (overwrites that bug's patches.json only).",
)
def write_concrete_patches(output: Path, session_id: str, bug_id: str):
    """
    CLI command to generate patches.json from the database.
    """
    with next(get_session()) as session:
        session_id_db = select(ExperimentSession.id).where(ExperimentSession.id == session_id)
        if not session.exec(session_id_db).first():
            click.echo(f"Session ID {session_id} not found.")
            return

        _write_concrete_patches(output, session_id, session, bug_id=bug_id)
        click.echo(f"Patches JSON generated at: {output}")