import json
import click
from pathlib import Path

from sprint.tgi.db.database import get_session
from sprint.tgi.models import AbstractPatch


@click.group()
def register_abstract_patches():
    """
    Group of commands to manage patches.
    """
    pass


@register_abstract_patches.command("register-baseline")
@click.argument("folder_path", type=click.Path(exists=True, file_okay=False, dir_okay=True, path_type=Path))
@click.option("--pfl", "is_pfl", is_flag=True, default=False, help="Mark patches as PFL (pfl=True). Updates existing patches' pfl flag.")
def register_baseline(folder_path: Path, is_pfl: bool):
    """
    Register SBFL baseline patches (step 1) or mark PFL patches (step 2).

    Step 1 (SBFL baseline): inserts patches with pfl=False, prunned=False, correct sbfl_score.
    Step 2 (PFL baseline, --pfl): sets pfl=True on existing patches; inserts PFL-only patches.
    """
    pfl_only_log = []
    total_newly_registered = 0
    total_updated = 0

    with next(get_session()) as session:
        for json_file in folder_path.rglob("convert_ir_patches.json"):
            bug_id = json_file.parent.name
            click.echo(f"📁 Processing {json_file} for bug `{bug_id}`...")

            try:
                data = json.loads(json_file.read_text())
            except json.JSONDecodeError as e:
                click.echo(f"❌ Failed to parse {json_file}: {e}", err=True)
                exit(1)

            newly_registered = 0
            updated = 0

            try:
                for item in data:
                    if item['rewriting_succeed'] is False:
                        continue
                    ap = AbstractPatch(
                        bug_id=bug_id,
                        procname=item['patch']['procname'],
                        line_from=item['line_range'][0],
                        line_to=item['line_range'][1],
                        pfl=is_pfl,
                        prunned=False,
                        **item['patch']['source_location'],
                        **item)
                    db_ap = session.query(AbstractPatch).filter_by(
                        bug_id=bug_id,
                        file=ap.file,
                        line=ap.line,
                        rewritten_source=ap.rewritten_source,
                    ).first()

                    if db_ap:
                        if is_pfl:
                            db_ap.pfl = True
                        else:
                            db_ap.sbfl_score = ap.sbfl_score
                        updated += 1
                    else:
                        session.add(ap)
                        newly_registered += 1
                        if is_pfl:
                            pfl_only_log.append({
                                "bug_id": bug_id,
                                "file": ap.file,
                                "line": ap.line,
                                "sbfl_score": ap.sbfl_score,
                            })

                session.commit()
            except Exception as e:
                click.echo(f"❌ Error while processing bug {bug_id}: {e}", err=True)
                session.rollback()
                continue

            total_newly_registered += newly_registered
            total_updated += updated

    click.echo(f"\n📊 Total Summary")
    click.echo(f"  ✅ Newly registered: {total_newly_registered}")
    click.echo(f"  🔁 Updated:          {total_updated}")

    if is_pfl and pfl_only_log:
        log_path = Path("pfl_only_patches.log")
        with log_path.open("w") as f:
            for entry in pfl_only_log:
                f.write(f"{entry['bug_id']}\t{entry['file']}:{entry['line']}\tsbfl_score={entry['sbfl_score']}\n")
        click.echo(f"⚠️  {len(pfl_only_log)} PFL-only patches (sbfl_score=1.0) logged to {log_path}")


@register_abstract_patches.command()
@click.argument("folder_path", type=click.Path(exists=True, file_okay=False, dir_okay=True, path_type=Path))
@click.option("--pfl", "is_pfl", is_flag=True, default=False,
              help="Only update patches with pfl=True (for PFL-only patches not in SBFL).")
def mark_pruned(folder_path: Path, is_pfl: bool):
    """
    Set prunned=False for APs in template output, prunned=True for those absent.

    Use --pfl to restrict updates to PFL-only patches (pfl=True), so SBFL patches
    already processed in a prior run are not overwritten.
    """
    pfl_only_pruned_log = []

    with next(get_session()) as session:
        total_pruned = 0
        total_survived = 0
        for json_file in folder_path.rglob("convert_ir_patches.json"):
            bug_id = json_file.parent.name
            click.echo(f"📁 Processing {json_file} for bug `{bug_id}`...")

            try:
                data = json.loads(json_file.read_text())
            except json.JSONDecodeError as e:
                click.echo(f"❌ Failed to parse {json_file}: {e}", err=True)
                exit(1)

            # Build set of survived APs from template JSON
            survived = set()
            for item in data:
                if item['rewriting_succeed'] is False:
                    continue
                survived.add((
                    item['patch']['source_location']['file'],
                    item['patch']['source_location']['line'],
                    item['rewritten_source'],
                ))

            # Set prunned=False for survived, prunned=True for pruned
            query = session.query(AbstractPatch).filter_by(bug_id=bug_id)
            if is_pfl:
                query = query.filter(AbstractPatch.pfl == True)
            all_aps = query.all()
            for ap in all_aps:
                key = (ap.file, ap.line, ap.rewritten_source)
                if key not in survived:
                    ap.prunned = True
                    total_pruned += 1
                    if is_pfl:
                        pfl_only_pruned_log.append(f"{bug_id}\t{ap.file}:{ap.line}")
                else:
                    ap.prunned = False
                    total_survived += 1

            try:
                session.commit()
            except Exception as e:
                click.echo(f"❌ Error while processing bug {bug_id}: {e}", err=True)
                session.rollback()
                continue

    click.echo(f"✅ Survived (prunned=False): {total_survived}")
    click.echo(f"🗑️  Pruned (prunned=True):   {total_pruned}")

    if is_pfl and pfl_only_pruned_log:
        log_path = Path("pfl_only_pruned.log")
        with log_path.open("w") as f:
            f.write("\n".join(pfl_only_pruned_log) + "\n")
        click.echo(f"⚠️  {len(pfl_only_pruned_log)} PFL-only patches marked pruned logged to {log_path}")
