import os
from pathlib import Path
import sys
import json
import tempfile
import subprocess
import time
from dataclasses import dataclass
import click
from sqlalchemy import create_engine
from sqlalchemy.pool import NullPool
from sqlalchemy.orm import sessionmaker
from datetime import datetime
from sqlmodel import SQLModel


import utils
from dotenv import load_dotenv
from models import Patch, PlausibleResult, ValidationFlag, ValidationResult, AbstractPatch, ConcretePatch

load_dotenv()

D4J_HOME = os.environ["D4J_HOME"]
DEFECTS4J = f"{D4J_HOME}/framework/bin/defects4j"
os.environ["LC_ALL"] = "en_US.UTF-8"
os.environ["LANG"] = "en_US.UTF-8"
os.environ["DATABASE_URL"] = "postgresql://sprint:sprint@localhost/validator_db"

PRIORITY = {
    "PASS": 0,
    "TEST_FAILURE": 1,
    "TIMEOUT": 2,
    "COMPILATION_FAILURE": 3
}


def validate_patch(
        session,
        bug_dir,
        patch: Patch,
        idx,
        timeout,
        ignore_db,
        record_plausible,
        ap_id,
        session_id=None,
):
    """
    Patch validation logic extracted into a separate function. Usable in multiprocess environments.
    """
    # look up or create Patch in DB
    db_patch = session.query(Patch).filter_by(
        bug_id=patch.bug_id,
        source_path=patch.source_path,
        line_from=patch.line_from,
        line_to=patch.line_to,
        patch_code=patch.patch_code
    ).first()

    if not db_patch:
        assert(not record_plausible)
        db_patch = Patch(
            bug_id=patch.bug_id,
            source_path=patch.source_path,
            line_from=patch.line_from,
            line_to=patch.line_to,
            patch_code=patch.patch_code
        )
        session.add(db_patch)
        session.commit()


    # look up ValidationResult
    if not ignore_db:
        db_result = session.query(ValidationResult).filter_by(
            patch_id=db_patch.id
        ).first()

        if record_plausible:
            assert(db_result is not None)

        if db_result:
            click.secho(
                f"[{idx}] {patch.bug_id} PID: {db_patch.id} VID: {db_result.id} {patch.source_path} (cached) -> {db_result.flag.value}",
                fg='yellow'
            )
            if record_plausible and db_result.flag == ValidationFlag.PASS:
                pl_result = PlausibleResult(
                    patch_id=db_result.patch_id,
                    abstract_patch_id=ap_id,
                    session_id=session_id
                )
                if session.query(PlausibleResult).filter_by(
                    patch_id=db_result.patch_id,
                    abstract_patch_id=ap_id,
                    session_id=session_id
                ).first():
                    return db_result.flag
                session.add(pl_result)
                session.commit()

                click.secho(
                    f"[{idx}] PID: {db_patch.id} (PLAUSIBLE FOUND)",
                    fg='green'
                )
            return db_result.flag



    click.secho(
        f"[{idx}] {patch.bug_id} {patch.source_path} validation started...",
        fg='cyan'
    )

    _reset(bug_dir)
    patch.create_source(bug_dir, idx)
    comp = _compile(bug_dir)
    if comp is None:
        flag = ValidationFlag.COMPILATION_FAILURE
        failed_tests = None
        testing_time = None
    else:
        flag, failed_tests, testing_time = _test(bug_dir, timeout)

    result = ValidationResult(
        patch_id=db_patch.id,
        flag=flag,
        failed_tests=failed_tests,
        compilation_time=comp,
        testing_time=testing_time
    )
    if not ignore_db:
        session.add(result)
        session.commit()

    color = (
        'green' if flag.value == 'PASS'
        else 'red' if flag.value == 'TEST_FAILURE'
        else 'magenta'
    )
    click.secho(
        f"[{idx}] {patch.bug_id} {patch.source_path} -> {flag.value}",
        fg=color
    )
    return flag


def _reset(dir_):
    utils.execute('git reset --hard', dir=dir_, verbosity=0)

def _compile(dir_):
    start = time.time()
    try:
        res = utils.execute(f'{DEFECTS4J} compile', dir=dir_, verbosity=0)
        if res.return_code != 0:
            return None
        return time.time() - start
    except Exception:
        return None

def _test(dir_, timeout):
    start = time.time()
    res = utils.execute(f'timeout {timeout} {DEFECTS4J} test', dir=dir_, timeout=timeout, verbosity=0)
    elapsed = time.time() - start
    if res.return_code == 124:
        flag = ValidationFlag.TIMEOUT
        return flag, None, elapsed
    out = res.stdout
    fail_count = 0
    # find the 'Failing tests:' line from the end
    for l in reversed(out.splitlines()):
        if l.startswith('Failing tests:'):
            try:
                fail_count = int(l.split()[-1])
            except Exception:
                fail_count = 0
            break
    # determine result
    if fail_count == 0:
        flag = ValidationFlag.PASS
    else:
        flag = ValidationFlag.TEST_FAILURE
    return flag, fail_count, elapsed

def get_best_flag(flags):
    if not flags:
        return ""
    return sorted(flags, key=lambda x: PRIORITY.get(x, 99))[0]

def collect_patch_results(session, patches_json):
    data = json.load(open(patches_json))
    from collections import defaultdict
    bug_results = defaultdict(list)
    for p in data:
        patch = Patch(**{k: v for k, v in p.items() if k in Patch.model_fields})
        # measure Patch query time
        t0 = time.time()
        db_patch = session.query(Patch).filter_by(
            bug_id=patch.bug_id,
            source_path=patch.source_path,
            line_from=patch.line_from,
            line_to=patch.line_to,
            patch_code=patch.patch_code
        ).first()
        t1 = time.time()
        print(f"[LOG] Patch query: {patch.bug_id} {patch.source_path} {t1-t0:.4f}s")
        if db_patch:
            # measure ValidationResult query time
            t0 = time.time()
            db_result = session.query(ValidationResult).filter_by(
                patch_id=db_patch.id
            ).first()
            t1 = time.time()
            print(f"[LOG] ValidationResult query: {db_patch.id} {t1-t0:.4f}s")
            if db_result:
                bug_results[patch.bug_id].append(db_result.flag.value)
    return bug_results

@click.group()
def cli():
    pass

@cli.command(help="Defects4J Patch Validator")
@click.argument('bug_dir', type=click.Path(exists=True))
@click.argument('patches_json', type=click.Path(exists=True))
@click.option('--timeout', default=300, help='Per-test timeout')
@click.option('--db-url', envvar='DATABASE_URL', default=os.environ['DATABASE_URL'], help='DB URL')
@click.option('--ignore-db', is_flag=True, default=False, help='Ignore DB cache and validate all patches')
@click.option('--record-plausible', is_flag=True, default=False, help='Record only plausible patches in DB')
def validate(bug_dir: Path, patches_json, timeout, db_url, ignore_db, record_plausible):
    bug_dir = os.path.abspath(bug_dir)
    patches_json = os.path.abspath(patches_json)
    engine = create_engine(db_url, poolclass=NullPool)
    SQLModel.metadata.create_all(engine)
    Session = sessionmaker(bind=engine)
    session = Session()

    data = json.load(open(patches_json))
    patches = [Patch(**{k: v for k, v in p.items() if k in Patch.model_fields}) for p in data]

    click.secho(f"Starting validation of {len(patches)} patches!", fg='blue', bold=True)
    for idx, p in enumerate(patches, 1):
        if p.bug_id in ['Lang_17', 'Math_20']:
            continue # excluded because Lang_17 tests take too long

        validate_patch(
            session,
            bug_dir,
            p,
            idx,
            timeout,
            ignore_db,
            record_plausible,
            ap_id=p.abstract_patch_id,
            session_id=Path(patches_json).parent.parent.name,
        )

    session.close()

@cli.command(help="Generate a summary CSV of patch results per bug")
@click.argument('patches_json_dirs', nargs=-1, type=click.Path(exists=True))
@click.option('--db-url', envvar='DATABASE_URL', help='DB URL')
@click.option('--summary-csv', type=click.Path(), required=True, help='Path to summary CSV of patch results per bug')
def summary(patches_json_dirs, db_url, summary_csv):
    import glob
    engine = create_engine(db_url)
    SQLModel.metadata.create_all(engine)
    Session = sessionmaker(bind=engine)
    session = Session()

    # bulk query from entire DB just once
    all_patches = session.query(Patch).all()
    patch_map = {
        (p.bug_id, p.source_path, p.line_from, p.line_to, p.patch_code): p.id
        for p in all_patches
    }
    all_results = session.query(ValidationResult).all()
    result_map = {r.patch_id: r.flag.value for r in all_results}

    all_bug_ids = set()
    folder_results = []
    folder_names = [os.path.basename(d.rstrip('/')) for d in patches_json_dirs]

    for patches_dir in patches_json_dirs:
        bug_results = {}
        for bug_json in glob.glob(os.path.join(patches_dir, "*", "patches.json")):
            bug_id = os.path.basename(os.path.dirname(bug_json))
            data = json.load(open(bug_json))
            bug_results[bug_id] = []
            for p in data:
                key = (p["bug_id"], p["source_path"], p["line_from"], p["line_to"], p["patch_code"])
                patch_id = patch_map.get(key)
                if patch_id:
                    flag = result_map.get(patch_id)
                    if flag:
                        bug_results[bug_id].append(flag)
        folder_results.append(bug_results)
        all_bug_ids.update(bug_results.keys())

    all_bug_ids = sorted(all_bug_ids)
    header = ["BUG_ID"] + folder_names
    import csv
    with open(summary_csv, "w", newline='') as f:
        writer = csv.writer(f)
        writer.writerow(header)
        for bug_id in all_bug_ids:
            row = [bug_id]
            for bug_results in folder_results:
                flags = bug_results.get(bug_id, [])
                row.append(get_best_flag(flags))
            writer.writerow(row)
    click.secho(f"Summary CSV saved: {summary_csv}", fg='green')
    utils.upload_csv_to_google_sheet(
        csv_path=Path(summary_csv),
        script_url=os.environ["SUMMARY_GOOGLE_WEB_APP_URL"],
        sheet_id=os.environ["SUMMARY_GOOGLE_SHEET_ID"],
        tab_name=datetime.now().strftime("%y%m%d-%H%M"),
    ) 
    session.close()

if __name__ == "__main__":
    cli()