import json
import click
from pathlib import Path
from sqlmodel import select
from sprint.tgi.db.database import get_session
from sprint.tgi.models import AbstractPatch, ConcretePatch

@click.group()
def tokens():
    pass

@tokens.command()
@click.option(
    "--patches-dir",
    type=click.Path(exists=True, file_okay=False, dir_okay=True, path_type=Path),
    default="patches",
    help="Base directory containing session folders under patches/",
    required=True,
)
@click.option(
    "--output-dir",
    type=click.Path(exists=True, file_okay=False, dir_okay=True, path_type=Path),
    help="Output directory to save tokens.json files",
    required=True,
)
def token(patches_dir: Path, output_dir: Path):
    patches_dir = Path(patches_dir)

    with next(get_session()) as session:
        for setting_dir in patches_dir.iterdir():
            if not setting_dir.is_dir():
                continue
            setting = setting_dir.name

            for patches_file in setting_dir.rglob("patches.json"):
                try:
                    with patches_file.open(encoding="utf-8") as f:
                        patches_info = json.load(f)
                except Exception as e:
                    click.echo(f"⚠️ Failed to read {patches_file}: {e}")
                    continue

                for info in patches_info:
                    ap_id = info.get("abstract_patch_id")
                    bug_id = info.get("bug_id")

                    if not ap_id or not bug_id:
                        continue

                    # look up AP + CP in DB
                    ap = session.exec(
                        select(AbstractPatch).where(AbstractPatch.id == ap_id)
                    ).first()

                    ap_dir = output_dir / setting / "NFL" / Path(str(ap.bug_id)) / Path(str(ap.line)) / Path(str(ap.id))
                    if (ap_dir / 'tokens.json').exists():
                        continue

                    if not ap:
                        click.echo(f"⚠️ No AP {ap_id} found in DB")
                        continue

                    cp = session.exec(
                        select(ConcretePatch)
                        .where(ConcretePatch.abstract_patch_id == ap.id)
                        .where(ConcretePatch.session_id == setting)
                    ).first()

                    if not cp:
                        click.echo(f"⚠️ No CP found for AP {ap_id} in setting {setting}")
                        continue

                    ap_dir.mkdir(parents=True, exist_ok=True)

                    data = {
                        "input_tokens": cp.propmt_eval_count,
                        "output_tokens": cp.eval_count,
                    }

                    with (ap_dir / "tokens.json").open("w", encoding="utf-8") as f:
                        json.dump(data, f, indent=4, ensure_ascii=False)

                    click.echo(f"✅ Saved tokens.json for AP {ap.id} (setting={setting}) -> {ap_dir}")
