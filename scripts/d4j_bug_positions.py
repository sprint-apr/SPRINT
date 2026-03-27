from datetime import datetime
from pprint import pprint
from typing import List
from config import BENCHMARKS_LIST, RESOURCES_DIR
import utils
import re
import typer
import os
import subprocess

app = typer.Typer()
DISSECTION_DIR = os.getenv("DISSECTION_DIR")
if not DISSECTION_DIR:
    print("set DISSECTION_DIR")
    exit(1)

D4J_BENCHMARK_DIR = os.getenv("D4J_BENCHMARK_DIR")
if not D4J_BENCHMARK_DIR:
    print("set D4J_BENCHMARK_DIR")
    exit(1)

BUG_COMMIT_ID = "01454a1"


def find_nearest_deleted_lines(benchmark_dir, bug_id, filepath, deleted_line):
    with open(f"{benchmark_dir}/{bug_id}/{filepath}", 'r', encoding="iso-8859-1") as f:
        lines = f.readlines()

        if deleted_line > len(lines):
            deleted_line = len(lines) - 1

        ranges = list(range(0, deleted_line))
        ranges.reverse()

        for line in ranges:
            if lines[line] != "":
                min_line = line + 1
                break

        for line in range(deleted_line, len(lines)):
            if lines[line] != "":
                max_line = line + 1
                break

    return min_line, max_line


@app.command()
def collect_bug_positions(benchmark_dir: str, buggy_commit_id=BUG_COMMIT_ID):
    for bug_id in BENCHMARKS_LIST:
        git_diff = utils.execute(
            f"git diff --unified=0 -p {buggy_commit_id} {bug_id}", dir=DISSECTION_DIR).stdout

        diff_files = git_diff.split("diff --git a/")[1:]
        for diff_file in diff_files:
            deleted_files = re.findall(fr'a/{bug_id}/\S*', diff_file)
            assert (len(deleted_files) == 1)

            filepath = deleted_files[0].split(f"a/{bug_id}/")[1]
            if filepath.endswith(".java") is False:
                continue

            lines = []

            line_diffs = re.findall(r'@@ -\S*', diff_file)

            for line_diff in line_diffs:
                line_diff = line_diff.lstrip("@@ -")
                if "," in line_diff:
                    [line, length] = line_diff.split(",")
                else:
                    line = int(line_diff)
                    length = 1
                line, length = int(line), int(length)
                if length == 0:
                    before, after = find_nearest_deleted_lines(
                        benchmark_dir,
                        bug_id, filepath, line)
                    lines.append(f"{before}")
                    lines.append(f"{after}")
                elif length == 1:
                    lines.append(f"{line}")
                else:
                    lines.append(f"{line}-{line + length - 1}")

            lines = set(lines)
            lines = ",".join(lines)
            if lines == "":
                print(diff_file)
                exit(1)

            print(f"{bug_id}@{filepath}@{lines}")


def get_latest_abstract_patch(bug_id: str, ap_dir=None) -> List[str]:
    if ap_dir is None:
        pattern = re.compile(r'ap_(\d{4})_(\d{4})_baseline')
        ap_dirs = []
        for ap_dir_name in os.listdir(f"{D4J_BENCHMARK_DIR}/abstractPatches/"):
            match = pattern.match(ap_dir_name)
            if match:
                # extract month, day, hour, minute from folder name
                month_day, hour_minute = match.groups()
                month = int(month_day[:2])
                day = int(month_day[2:4])
                hour = int(hour_minute[:2])
                minute = int(hour_minute[2:4])
                
                # convert to datetime object
                ap_dir_date = datetime(datetime.now().year, month, day, hour, minute)
                
                # store folder name together with its date
                ap_dirs.append((ap_dir_name, ap_dir_date))

            # sort folders by date (most recent folder first)
            ap_dirs.sort(key=lambda x: x[1], reverse=True)
        ap_dir = ap_dirs[0][0]

    patches = utils.read_json_from_file(f"{D4J_BENCHMARK_DIR}/abstractPatches/{ap_dir}/{bug_id}/convert_ir_patches.json")
    return [patch["rewritten_source"] for patch in patches if patch["rewritten_source"]]
    

@app.command()
def diff(bug_id=os.path.basename(os.getcwd()), show_ap=None, show_chatrepair=True):
    if show_ap:
        print("\nAbstract patch:")
        aps = get_latest_abstract_patch(bug_id)
        pprint(aps)
    
    print("\nDeveloper's patch:")
    subprocess.run(
        f"git diff --unified=0 -p {BUG_COMMIT_ID} {bug_id}", cwd=DISSECTION_DIR,
        shell=True, env={"GIT_PAGER": "cat"})

    if show_chatrepair:
        print("\nChatRepair's patch:")
        if os.path.isfile(f"{RESOURCES_DIR}/ChatRepair_patches/{bug_id}.diff"):
            subprocess.run(
                f"cat {RESOURCES_DIR}/ChatRepair_patches/{bug_id}.diff", shell=True)
        else:
            print(" - No ChatRepair patch found")


if __name__ == "__main__":
    app()
