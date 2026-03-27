"""
Export FL4APR experiment results to SPRINT_scripts directory format.

Output structure:
  {output_dir}/patches/{session_id}/PFL/{bug_id}/{ap_id}/{patch_id}.diff
  {output_dir}/rawdata/{session_id}/NFL/{bug_id}/ap.json
"""
import json
import re
import subprocess
import tempfile
import os
import click
from pathlib import Path
from sqlalchemy import create_engine, text

LINE_LEVEL_RE = re.compile(r"^sed '\d+c\"<MASK>\"")

BATCH_DB_URL = "postgresql://sprint:sprint@localhost/batch"
VALIDATOR_DB_URL = "postgresql://sprint:sprint@localhost/validator_db"


def get_validation_map(validator_engine, bug_id: str) -> dict:
    """Returns {(source_path, line_from, line_to, patch_code): flag} for a bug."""
    with validator_engine.connect() as conn:
        rows = conn.execute(text("""
            SELECT p.source_path, p.line_from, p.line_to, p.patch_code, vr.flag
            FROM patches p
            JOIN validation_results vr ON vr.patch_id = p.id
            WHERE p.bug_id = :bug_id
        """), {"bug_id": bug_id}).fetchall()
    return {(r.source_path, r.line_from, r.line_to, r.patch_code): r.flag for r in rows}


def generate_diff(bug_dir: Path, bug_id: str, source_path: str, line_from: int, line_to: int, patch_code: str) -> str | None:
    """Generate unified diff by comparing original source vs patched version."""
    src = bug_dir / source_path
    if not src.exists():
        return None

    # Restore original source in case SPRINT analysis left modifications behind
    subprocess.run(['git', 'checkout', '--', source_path], cwd=bug_dir, capture_output=True)

    try:
        try:
            lines = src.read_text().splitlines(keepends=True)
        except UnicodeDecodeError:
            lines = src.read_text(encoding='ISO-8859-1').splitlines(keepends=True)
    except Exception:
        return None

    patched_lines = lines[:line_from - 1] + [patch_code + '\n'] + lines[line_to:]
    original_content = ''.join(lines)
    patched_content = ''.join(patched_lines)

    with tempfile.NamedTemporaryFile(mode='w', suffix='_a.java', delete=False) as f:
        f.write(original_content)
        orig_path = f.name
    with tempfile.NamedTemporaryFile(mode='w', suffix='_b.java', delete=False) as f:
        f.write(patched_content)
        patched_path = f.name

    try:
        result = subprocess.run(
            ['diff', '-u', orig_path, patched_path],
            capture_output=True, text=True
        )
        # diff -u returns 0 (identical) or 1 (different); 2 is error
        if result.returncode == 2:
            return None
        diff_lines = result.stdout.splitlines()
        if len(diff_lines) < 4:
            return None

        # Replace temp paths in header with meaningful names
        # diff -u output: [0] --- orig  [1] +++ patched  [2+] hunks
        diff_lines[0] = f"--- {bug_id}/{source_path}"
        diff_lines[1] = f"+++ {bug_id}/{source_path}"
        return '\n'.join(diff_lines) + '\n'
    finally:
        os.unlink(orig_path)
        os.unlink(patched_path)


@click.command()
@click.option('--session-id', required=True, help='Experiment session ID (e.g. gpt-4.1-nano_0310)')
@click.option('--patches-dir', required=True, type=Path, help='Dir containing {bug_id}/patches.json')
@click.option('--bugs-dir', required=True, type=Path, help='D4J bug checkout root (d4j_projects)')
@click.option('--output-dir', required=True, type=Path, help='Output root directory')
@click.option('--batch-db-url', default=BATCH_DB_URL, show_default=True)
@click.option('--validator-db-url', default=VALIDATOR_DB_URL, show_default=True)
def export_sprint_format(session_id, patches_dir, bugs_dir, output_dir, batch_db_url, validator_db_url):
    """Export FL4APR results to SPRINT_scripts analysis format."""
    batch_engine = create_engine(batch_db_url)
    validator_engine = create_engine(validator_db_url)

    pfl_output = output_dir / "patches" / session_id / "PFL"
    nfl_output = output_dir / "rawdata" / session_id / "NFL"

    bug_json_files = sorted(patches_dir.glob("*/patches.json"))
    click.secho(f"Found {len(bug_json_files)} bugs in {patches_dir}", fg='blue', bold=True)

    total_pass = 0
    total_ap = 0

    for patches_json in bug_json_files:
        bug_id = patches_json.parent.name
        bug_dir = bugs_dir / bug_id

        if not bug_dir.exists():
            click.secho(f"[SKIP] {bug_id}: bug dir not found", fg='yellow')
            continue

        data = json.loads(patches_json.read_text())
        val_map = get_validation_map(validator_engine, bug_id)

        # Export PASS patches as .diff files
        pass_count = 0
        path_counters = {}  # (ap_id, cp_id) -> next index, for deduplicating same cp_id
        for entry in data:
            key = (entry['source_path'], entry['line_from'], entry['line_to'], entry['patch_code'])
            if val_map.get(key) != 'PASS':
                continue

            ap_id = entry['abstract_patch_id']
            cp_id = entry['concrete_patch_id']

            diff_content = generate_diff(
                bug_dir, bug_id,
                entry['source_path'], entry['line_from'], entry['line_to'], entry['patch_code']
            )
            if diff_content is None:
                click.secho(f"  [WARN] {bug_id} ap={ap_id} cp={cp_id}: diff generation failed", fg='yellow')
                continue

            idx = path_counters.get((ap_id, cp_id), 0)
            path_counters[(ap_id, cp_id)] = idx + 1
            filename = f"{cp_id}.diff" if idx == 0 else f"{cp_id}_{idx}.diff"
            diff_path = pfl_output / bug_id / str(ap_id) / filename
            diff_path.parent.mkdir(parents=True, exist_ok=True)
            diff_path.write_text(diff_content)
            pass_count += 1

        # Export ap.json from AbstractPatch DB
        with batch_engine.connect() as conn:
            rows = conn.execute(text("""
                SELECT id, bug_id, file, line, sbfl_score, pfl, prunned, rewriting_instr
                FROM abstractpatch
                WHERE bug_id = :bug_id
                ORDER BY sbfl_score DESC
            """), {"bug_id": bug_id}).fetchall()

        # prunned=True in FL4APR means the patch was pruned away (does not remain)
        ap_data = [
            {
                "bug_id": r.bug_id,
                "ap_id": r.id,
                "file": r.file,
                "line": r.line,
                "sbfl_score": r.sbfl_score,
                "remains_after_prunning": not r.prunned if r.prunned is not None else True,
                "pfl": r.pfl if r.pfl is not None else False,
                "is_line_level": bool(LINE_LEVEL_RE.match(r.rewriting_instr or "")),
            }
            for r in rows
        ]

        ap_json_path = nfl_output / bug_id / "ap.json"
        ap_json_path.parent.mkdir(parents=True, exist_ok=True)
        ap_json_path.write_text(json.dumps(ap_data, indent=2))

        total_pass += pass_count
        total_ap += len(ap_data)
        click.secho(f"[{bug_id}] PASS diffs: {pass_count}, APs: {len(ap_data)}", fg='green')

    click.secho(f"\nDone. Total PASS diffs: {total_pass}, Total APs: {total_ap}", fg='blue', bold=True)


if __name__ == '__main__':
    export_sprint_format()
