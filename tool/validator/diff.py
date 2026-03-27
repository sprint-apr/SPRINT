import os, json, tempfile, subprocess, difflib, click
from dotenv import load_dotenv
from sqlalchemy import create_engine, select
from sqlalchemy.orm import sessionmaker

from models import Base, Patch, ValidationFlag, ValidationResult

load_dotenv()

D4J_HOME = os.environ["D4J_HOME"]
DEFECTS4J = f"{D4J_HOME}/framework/bin/defects4j"
os.environ["LC_ALL"] = "en_US.UTF-8"
os.environ["LANG"] = "en_US.UTF-8"
os.environ["DATABASE_URL"] = "postgresql://sprint:sprint@localhost/validator_db"

def read_file(path):
    try:
        return open(path, encoding="utf-8").read()
    except UnicodeDecodeError:
        return open(path, encoding="latin-1").read()
    except FileNotFoundError:
        return None

def get_original_commited_source(bug_id, repo_dir, rel_path):
    """repo_path = BUGS/{bug_id}, rel_path = source/..."""
    try:
        return subprocess.check_output(
            ["git", "-C", repo_dir, "show", f"HEAD:{rel_path}"],
            text=True
        )
    except subprocess.CalledProcessError:
        return None

def make_diff(orig, patched, bug_id, rel_path):
    with tempfile.TemporaryDirectory() as td:
        a_tmp = os.path.join(td, bug_id, rel_path)
        os.makedirs(os.path.dirname(a_tmp), exist_ok=False)
        b_tmp = os.path.join(td, "b.java")
        open(a_tmp, "w", encoding="utf-8").write(orig)
        open(b_tmp, "w", encoding="utf-8").write(patched)

        # run diff (with path strings set to our desired values)
        r = subprocess.run(
            [
                "git", "diff", "--no-index",
                "--",
                os.path.join(bug_id, rel_path),
                b_tmp,
            ],
            cwd=td, capture_output=True, text=True
        )
        return r.stdout



@click.command()
@click.argument("bugs_root", type=click.Path(exists=True, file_okay=False))
@click.argument("patches_json", type=click.Path(exists=True, dir_okay=False))
@click.option('--db-url', envvar='DATABASE_URL', default=os.environ['DATABASE_URL'], help='DB URL')
@click.option("--out-dir", "-o", type=click.Path(file_okay=False),
              help="Output session directory (default: folder containing patches.json)")
def main(bugs_root, patches_json, out_dir, db_url):
    """Generate diff files for PASS patches using BUGS_ROOT, PATCHES_JSON, and DB"""
    out_dir = out_dir or os.path.dirname(os.path.abspath(patches_json))
    os.makedirs(out_dir, exist_ok=True)

    engine = create_engine(db_url)
    Session = sessionmaker(bind=engine)
    session = Session()

    patches = json.load(open(patches_json, encoding="utf-8"))

    orig = None
    for idx, p in enumerate(patches):
        bug_id     = p["bug_id"]
        source_rel = p["source_path"]
        lf, lt     = p["line_from"], p["line_to"]
        code       = p["patch_code"]

        if orig is None:
            orig = get_original_commited_source(bug_id, 
                                                os.path.join(bugs_root, bug_id),
                                                source_rel)
            if orig is None:
                click.echo(f"[WARN] {bug_id}:{source_rel} original source not found", err=True)
                exit(1)

        # look up patch_id in DB
        q = (session.query(Patch)
             .filter_by(bug_id=bug_id,
                        source_path=source_rel,
                        line_from=lf,
                        line_to=lt,
                        patch_code=code))
        cp = q.first()
        if not cp:
            click.echo(f"[WARN] {bug_id}:{source_rel}:{lf}-{lt} matching failed", err=True)
            exit(1)

        db_result = session.query(ValidationResult).filter_by(
            patch_id=cp.id
        ).first()
        if db_result.flag != ValidationFlag.PASS:   # check models.py for flag / status fields
            continue


        lines = orig.splitlines(True)
        fixed = "".join(lines[:lf-1]) + code + ("\n" if not code.endswith("\n") else "") + "".join(lines[lt:])
        diff  = make_diff(orig, fixed, bug_id, source_rel)

        out_path = os.path.join(out_dir, f"{cp.id}.diff")
        with open(out_path,"w",encoding="utf-8") as f:
            f.write(diff)
        click.echo(f"WROTE {out_path}")

    session.close()

if __name__ == "__main__":
    main()
