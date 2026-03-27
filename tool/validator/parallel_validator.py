import os
import json
from pathlib import Path
from multiprocessing import Pool
import click
from validator import validate

os.environ["DATABASE_URL"] = "postgresql://sprint:sprint@localhost/validator_db"


def get_bug_patch_pairs(bugs_dir, patches_root_dir):
    bugs_dir = Path(bugs_dir)
    patches_root_dir = Path(patches_root_dir)
    pairs = []
    for patch_json in patches_root_dir.glob("*/patches.json"):
        bug_id = patch_json.parent.name
        bug_dir = bugs_dir / bug_id
        if bug_dir.exists():
            pairs.append((bug_dir, patch_json))
    sorted_pairs = sorted(pairs, key=lambda x: x[0].name)
    return sorted_pairs

def validate_single(args):
    bug_dir, patch_json, timeout, db_url = args
    from click.testing import CliRunner
    runner = CliRunner()
    result = runner.invoke(
        validate,
        [str(bug_dir), str(patch_json), '--timeout', str(timeout), '--db-url', db_url]
    )
    err = None
    if result.exit_code != 0:
        err = str(result.exception) if result.exception else result.output[-500:] if result.output else "unknown error"
    return (bug_dir, patch_json.parent, result.exit_code, err)

@click.command(help="Parallel Defects4J Patch Validator")
@click.argument('bugs_dir', type=click.Path(exists=True))
@click.argument('patches_root_dir', type=click.Path(exists=True))
@click.option('--timeout', default=300, help='Per-test timeout')
@click.option('--db-url', envvar='DATABASE_URL', required=True, help='DB URL')
@click.option('--jobs', default=8, help='Number of parallel jobs')
def main(bugs_dir, patches_root_dir, timeout, db_url, jobs):
    pairs = get_bug_patch_pairs(bugs_dir, patches_root_dir)
    total = len(pairs)
    click.secho(f"Starting parallel validation for {total} bugs!", fg='blue', bold=True)
    args_list = [(bug_dir, patch_json, timeout, db_url) for bug_dir, patch_json in pairs]
    completed = 0
    with Pool(processes=jobs) as pool:
        for bug_dir, patch_dir, exit_code, err in pool.imap_unordered(validate_single, args_list):
            completed += 1
            remaining = total - completed
            msg = f"[{bug_dir.name}] {exit_code} ({completed}/{total}, {remaining} remaining)"
            if err:
                msg += f" | {err}"
            click.secho(msg, fg='green' if exit_code == 0 else 'red')

if __name__ == "__main__":
    main()