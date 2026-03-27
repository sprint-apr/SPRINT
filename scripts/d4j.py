#!/usr/bin/python3.8
import argparse
import glob
import logging
import os
import time
import functools
from functools import partial
from multiprocessing import Pool
from pathlib import Path
import ochiai

import pprint
import utils
import tracer
from pprint import pprint
from bug import Bug
from config import *

ROOT_DIR = os.getcwd()
SCRIPT_DIR = f"{os.path.dirname(os.path.realpath(__file__))}"

# Single function bugs
BENCHMARKS_LIST = [bug_id.replace("\n", "") for bug_id in open(
    f'{SCRIPT_DIR}/sf.lst', 'r').readlines()]

# SPRINT_PLDI + ChatRepair + TARE + ITER
TARGET_LIST = [bug_id.replace("\n", "") for bug_id in open(
    f'{SCRIPT_DIR}/target.lst', 'r').readlines()]

def main_target_bugs():
    return BENCHMARKS_LIST 


def multiprocess_with_logging_result(logpath, num_processes, task, args):
    with open(logpath, "w") as f:
        f.write(f'# execution time: {time.strftime("%Y-%m-%d %H:%M")}')
        with Pool(processes=num_processes) as p:
            for result in p.imap_unordered(task, args):
                print(result)
                f.write(result + "\n")
                f.flush()


def init_bugs(bugs_dir, targets, exclude):
    bug_dirs = [
        os.path.abspath(dir)
        for dir in glob.glob(f"{bugs_dir}/*_*")
        if os.path.isdir(dir) and os.path.exists(f"{dir}/defects4j.build.properties") and os.path.basename(dir) in targets
    ]

    with Pool(processes=24) as p:
        bugs = list(p.imap_unordered(Bug.from_dir, bug_dirs))

    for dir in bug_dirs:
        if os.path.exists(socket := (f"{dir}/infer-out/sqlite_write_socket")):
            os.remove(socket)

    assert all([b.build_type == "defects4j" for b in bugs])

    if exclude != None:
        excludes = sum(
            [
                Path(path).read_text().strip().split()
                for path in exclude.split(",")
            ],
            [],
        )
        bugs = [b for b in bugs if b.id not in excludes]
        print(f"{len(excludes)} bugs are excluded: {excludes}")
    return bugs


def checkout_all_bugs(bugs_dir, targets):
    def is_not_checkouted(bug_id): return not os.path.isfile(
        f"{bugs_dir}/{bug_id}/defects4j.build.properties") or not os.path.isfile(f"{bugs_dir}/{bug_id}/ochiai.txt")
    bug_ids = [b.replace(" ", "_") for b in BENCHMARKS_LIST]
    bug_ids = filter(is_not_checkouted, bug_ids)
    bug_ids = [bug_id for bug_id in bug_ids if bug_id in targets]

    with Pool(processes=24) as p:
        list(p.imap_unordered(partial(Bug.d4j_clone, bugs_dir=bugs_dir), bug_ids))

    for bug_id in bug_ids:
        if is_not_checkouted(bug_id):
            print(f"{ERROR}: failed to checkout {bug_id}")

    return init_bugs(bugs_dir, BENCHMARKS_LIST, None)


def capture(bug):
    log = open("d4j.capture.log", "a")
    completed = bug.capture_all()
    if completed.return_code != 0:
        print(f"{ERROR}: {bug.id} is not captured")
    log.write(msg := f"{bug.id}, {completed.return_code}\n")
    log.flush()
    log.close()


def capture_all_bugs(bugs, jobs=24):
    log = open("d4j.capture.log", "w")
    logging.info(f"Capturing total {len(bugs)} defects4j bugs")
    with Pool(processes=jobs) as p:
        p.map(partial(capture), bugs)
    log.close()


def preanal(bug: Bug):
    TIMEOUT = 600
    script_cmd = f"timeout {TIMEOUT} python3 {SCRIPT_DIR}/sprint.py analyze --pre-only"
    ret = utils.execute(script_cmd, dir=bug.project_root_dir,
                        timeout=(TIMEOUT + 1))

    log = open("d4j.preanal.log", "a")
    if os.path.exists(f"{bug.project_root_dir}/sprint-preanalysis-result") is False:
        log.write("Failed to execute preanalysis (or infer)")
        print(f"{bug.id}: {ERROR} Failed to execute preanalysis (or infer)")
        return

    with open(f"{bug.project_root_dir}/sprint-preanalysis-result", "r") as f:
        result_type = f.read().strip()

    if result_type == "Unreachable":
        log.write(f"{bug.id}, UNREACHABLE, {ret.time:.1f}\n")
        print(f"{bug.id}: {WARNING} some methods are UNREACHABLE from tests {ret.time:.1f}")
    elif result_type == "Default":
        log.write(f"{bug.id}, DEFAULT, {ret.time:.1f}\n")
        print(f"{bug.id}: {WARNING} preanalysis failed. use default callgraph {ret.time:.1f}")
    else:
        log.write(f"{bug.id}, SUCCESS, {ret.time:.1f}\n")
        print(f"{bug.id}: {SUCCESS} preanalysis succeeded {ret.time:.1f}")

    log.flush()
    log.close()


def analyze_bug_only(bug: Bug, pfl, exnchecker, no_test):
    if pfl:
        TIMEOUT = 1200
    else:
        TIMEOUT = 1800

    script_cmd = f"timeout {TIMEOUT} python3 {SCRIPT_DIR}/sprint.py analyze --skip-preanal \
        {'--pfl' if pfl else ''} --pool {os.getpid() % 4} {'--exn-only' if exnchecker else '--main-only'} {'--no-test' if no_test else ''}"
    utils.remove_file_if_exists(f"{bug.project_root_dir}/infer-out/logs")
    utils.remove_file_if_exists(f"{bug.project_root_dir}/results.csv")
    utils.remove_file_if_exists(f"{bug.project_root_dir}/feasible_fault*")
    ret = utils.execute(script_cmd, dir=bug.project_root_dir, timeout=TIMEOUT)

    has_sat_abs_patches = is_correctly_localized(bug)

    if exnchecker:
        log_anal = open("d4j.analyze.exn.log", "a")
    else:
        log_anal = open("d4j.analyze.log", "a")

    task = "exnchecker" if exnchecker else "diff-analyze"

    fail_log = open(f"{bug.project_root_dir}/analyze.exn.fail.log", 'w')

    if ret.return_code == 12:
        print(f"{FAIL}-preanal: {task} {bug.id} {ret.time:.1f}")
        log_anal.write(
            msg := f"{bug.id}, {ret.time:.1f}, FAIL-preanal{ret.return_code}\n")
    elif ret.time >= TIMEOUT:
        print(f"{TIMEOUT}: {task} {bug.id} {ret.time:.1f}")
        log_anal.write(msg := f"{bug.id}, {ret.time:.1f}, TIMEOUT\n")
    elif ret.return_code == 11:
        fail_log.write(f"{ret.stdout}\n{ret.stderr}")
        print(f"{WARNING}: failed to correctly analyze {bug.id}")
        log_anal.write(msg := f"{bug.id}, {ret.time:.1f}, UNSOUND\n")
    elif ret.return_code == 13:
        fail_log.write(f"{ret.stdout}\n{ret.stderr}")
        print(f"{WARNING}: failed to analyze with dyninfo {bug.id} (mismatched call)")
        log_anal.write(msg := f"{bug.id}, {ret.time:.1f}, SUCCEED, used pre-pruning (because of call)\n")
    elif ret.return_code == 14:
        fail_log.write(f"{ret.stdout}\n{ret.stderr}")
        print(f"{WARNING}: failed to analyze with dyninfo {bug.id} (mismatched prune)")
        log_anal.write(msg := f"{bug.id}, {ret.time:.1f}, SUCCEED, used pre-pruning (because of prune)\n")
    elif ret.return_code != 0:
        print(f"{FAIL}: {task} {bug.id} {ret.time:.1f}")
        fail_log.write(f"{ret.stdout}\n{ret.stderr}")
        log_anal.write(
            msg := f"{bug.id}, {ret.time:.1f}, FAIL-{ret.return_code}\n")
    elif has_sat_abs_patches:
        print(f"{SUCCESS}: {task} {bug.id} {ret.time:.1f}")
        log_anal.write(msg := f"{bug.id}, {ret.time:.1f}, SUCCEED\n")
    else:
        print(f"{FAIL}-localize: {task} {bug.id} {ret.time:.1f}")
        log_anal.write(msg := f"{bug.id}, {ret.time:.1f}, FAIL\n")

    log_anal.flush()
    log_anal.close()


def analyze_bugs_only(bugs, pfl, exnchecker, no_test):
    logging.info(f"Capturing total {len(bugs)} defects4j bugs")
    if exnchecker:
        log_anal = open("d4j.analyze.exn.log", "w")
    else:
        log_anal = open("d4j.analyze.log", "w")

    with Pool(processes=4) as p:
        p.map_async(
            partial(analyze_bug_only, pfl=pfl,
                    exnchecker=exnchecker, no_test=no_test), bugs
        ).get()


def build_defects4j_projects(bugs):
    bugs = set(bugs)
    bugs_with_old_ant = set(
        filter(lambda bug: bug.ant_version == "1.8.4", bugs))

    # Build non-Lang projects first so that bug can be built with the proper ant version.
    with Pool(processes=32) as p:
        msgs = list(p.imap_unordered(Bug.d4j_build, bugs - bugs_with_old_ant))

    with Pool(processes=32) as p:
        msgs += list(x for x in p.imap_unordered(Bug.d4j_build,
                     bugs_with_old_ant))

    with open("d4j.build.log", "w") as f:
        f.write("\n".join(msgs))


def is_correctly_localized(bug):
    if os.path.isfile(file := f"{bug.project_root_dir}/feasible_abs_patches"):
        lines = open(file, "r").readlines()
        correct_lines = bug.get_correct_lines()
        for line in lines:
            for correct_line in correct_lines:
                if correct_line in line:
                    return True
    return False


def has_correct_fault(bug):
    if os.path.isfile(file := f"{bug.project_root_dir}/results.csv"):
        lines = open(file, "r").readlines()
        correct_lines = bug.get_correct_lines()
        for line in lines:
            if "ExistExnSat" in line or ",Sat" in line:
                for correct_line in correct_lines:
                    if correct_line in line:
                        return True
        return False

    else:
        return False


def correct_fault_ranking(bug, filename):
    if os.path.isfile(file := f"{bug.project_root_dir}/{filename}"):
        lines = list(open(file, "r").readlines())
        correct_lines = bug.get_correct_lines()
        for i in range(0, len(lines)):
            line = lines[i]
            for correct_line in correct_lines:
                if correct_line in line:
                    # print (f"find correct line {line} at {bug.id}")
                    return lines[: i + 1]
        return []

    else:
        return []


@functools.lru_cache(maxsize=None)
def sprint_pldi_plausible_result():
    results = {bug_id: False for bug_id in BENCHMARKS_LIST}
    with open(f"{RESOURCES_DIR}/sprint_pldi.lst", 'r') as f:
        for bug_id in f.readlines():
            bug_id = bug_id.rstrip("\n")
            results[bug_id] = True
    return results

@functools.lru_cache(maxsize=None)
def tare_correct_result():
    results = {bug_id: False for bug_id in BENCHMARKS_LIST}
    with open(f"{RESOURCES_DIR}/tare.lst", 'r') as f:
        for line in f.readlines():
            [repo, bug_ids] = line.split(": ")
            for id in bug_ids.split(", "):
                id = id.rstrip("\n")
                results[f"{repo}_{id}"] = True
    return results


@functools.lru_cache(maxsize=None)
def iter_result():
    results = {bug_id: False for bug_id in BENCHMARKS_LIST}
    with open(f"{RESOURCES_DIR}/iter.lst", 'r') as f:
        for bug_id in f.readlines():
            bug_id = bug_id.rstrip("\n")
            results[bug_id] = True
    return results


@functools.lru_cache(maxsize=None)
def d4c_result():
    results = {bug_id: False for bug_id in BENCHMARKS_LIST}
    with open(f"{RESOURCES_DIR}/d4c.lst", 'r') as f:
        for bug_id in f.readlines():
            bug_id = bug_id.rstrip("\n")
            results[bug_id] = True
    return results


def does_sota_fix(bug_id):
    return tare_correct_result()[bug_id] or iter_result()[bug_id]


def comparison_with_existing_result(bug_id, is_success):
    if d4c_result()[bug_id]:
        return "D4C-fixed"
    elif is_success:
        return "Improved"
    else:
        return "Refineable"


def evaluate_bug(bug):
    correct_localized = is_correctly_localized(bug)
    if os.path.isfile(file := f"{bug.project_root_dir}/results.csv"):
        lines = open(file, "r").readlines()
        abs_patches_all = len(lines) - 1

    else:
        abs_patches_all = 0

    feasible_abs_patches = correct_fault_ranking(
        bug, "feasible_abs_patches")
    normalized_abs_patches = [
        line.split(":[")[0]
        for line in correct_fault_ranking(bug, "feasible_fault_partition")
    ]

    # compute sbfl rank
    correct_lines = bug.get_correct_lines2()
    sbfl_rank = -1
    _rank = 0
    for (cp, line, _) in ochiai.parse(bug.id):
        ochiai_line = cp.replace(".", "/") + f".java:{line}"
        _rank += 1
        for correct_line in correct_lines:
            if ochiai_line in correct_line:
                sbfl_rank = _rank
                break

    ap_rank = len(feasible_abs_patches)

    if bug.id in TARGET_LIST:
        if correct_localized:
            is_target_fixed = "Target-Fixed"
        else:
            is_target_fixed = "Target-Failed"
    else:
        is_target_fixed = "Not-Target"

    return {
        "BugId": f"{bug.id.split('_')[0]} {bug.id.split('_')[1]}",
        "Rank": sbfl_rank,
        "#APatches": abs_patches_all,
        "Rank_AP": ap_rank,
        "IsTarget": is_target_fixed,
        "IsCorrect": correct_localized,
    }


def evaluate(bugs, setting_name=None, output_dir=None):
    results = []

    for bug in bugs:
        result = evaluate_bug(bug)

        # line-level results
        feasible_abs_patches = correct_fault_ranking(
            bug, "feasible_abs_patches")

        wrong_lines = [line.split("_WrongExp")[0]
                       for line in feasible_abs_patches if "_WrongExp" in line]
        skip_lines = [line.split("_ShouldSkip")[0]
                      for line in feasible_abs_patches if "_ShouldSkip" in line]
        side_effects = [line.split("_SideEffect")[
            0] for line in feasible_abs_patches if "_SideEffect" in line]
        missing_lines = (skip_lines + [line.split("_MissingError")[0]
                         for line in feasible_abs_patches if "_MissingError" in line] + side_effects)
        fault_lines = wrong_lines + missing_lines

        result["#FaultLine"] = len(set(fault_lines))
        result["#FaultLine"] = len(set(fault_lines))
        result["#WrongLine"] = len(set(wrong_lines))
        result["#MissingLine"] = len(set(missing_lines))

        results.append(result)

    results = sorted(
        results,
        key=lambda x: (
            x["IsTarget"],
            x["BugId"].split(" ")[0],
        ),
        reverse=True,
    )
    if setting_name:
        filename = "results.%s_%s.pretty" % (
            setting_name,
            str(time.strftime("%m%d", time.localtime())),
        )
    else:
        filename = "results_%s.pretty" % str(
            time.strftime("%m%d_%I%M", time.localtime())
        )

    if output_dir:
        filename = os.path.join(output_dir, filename)
    utils.pretty_print_dict_to_csv(filename, results)
    number_of_correct = len(
        list(filter(lambda x: x["IsCorrect"], results)))
    print(f"#correctly analyzed: {number_of_correct}")

    return filename


def evaluate_ap(bugs, setting):
    results = []

    def correct_ap_rank(bug):
        lines = bug.get_correct_lines2()
        name = f"ap_{setting}"
        jsonpath = f"{ROOT_DIR}/abstractPatches/{name}/{bug.id}/convert_ir_patches.json"
        if os.path.isfile(jsonpath) and os.path.getsize(jsonpath):
            result = 0
            correct_line = None
            patches = utils.read_json_from_file(jsonpath)
            num_patches = len(patches)
            for patch in patches:
                patch_loc = patch["patch"]["source_location"]
                loc_line = patch_loc["file"] + ":" + str(patch_loc["line"])
                if correct_line and correct_line != loc_line:
                    return (num_patches, result + 1)
                if loc_line in lines:
                    correct_line = loc_line
                result += 1
            if correct_line:
                return (num_patches, result)
            else:
                return (num_patches, -1)
        else:
            print(f"{ERROR}: failed to find {jsonpath} for {bug.id}")
            return (0, 0)

    for bug in bugs:
        result = evaluate_bug(bug)

        _, rank = correct_ap_rank(bug)

        comparison_result = comparison_with_existing_result(bug.id, 0 < rank)
        result.update(
            {
                "Rank_Patch": rank,
                "VsD4C": comparison_result
            })

        results.append(result)

    results = sorted(
        results,
        key=lambda x: (x["IsCorrect"], x["BugId"].split(" ")
                       [0], x["Rank_Patch"], x["VsD4C"]),
        reverse=True,
    )

    number_of_correct = len(
        list(filter(lambda x: x["IsCorrect"], results)))
    print(f"#correctly analyzed: {number_of_correct}")

    filename = "results.ap.%s.pretty" % (setting)
    utils.pretty_print_dict_to_csv(filename, results)
    return filename


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "mode",
        choices=[
            "d4j-build",
            "init",
            "capture",
            "checkout",
            "analyze_bug_only",
            "preanal",
            "evaluate",
            "tracer",
            "enum-concrete",
            "enum-ap",
            "utils",
        ],
    )
    parser.add_argument("bugs_dir")
    parser.add_argument(
        "--pfl", help="Run FL in PFL mode", default=False, action="store_true"
    )
    parser.add_argument(
        "--all", help="Run all benchmarks", default=False, action="store_true"
    )
    parser.add_argument(
        "--prune_mode",
        help="mode to run FL",
        default="all",
        choices=["template", "baseline", "line", "all"],
    )
    parser.add_argument(
        "--exnchecker", help="Run FL in PFL mode", default=False, action="store_true"
    )
    parser.add_argument("--target", help="Specifies target bug id file")
    parser.add_argument("--no-test", action='store_true',
                        default=False, help="run analyze without test information")
    parser.add_argument("--setting", default=str(
            time.strftime("%m%d_%I%M", time.localtime())
        ), help="setting name")
    parser.add_argument(
        "--exclude", help="Specifies bug id files to exclude running")
    parser.add_argument(
        "--validation-result",
        help="Specifies file name to print validation results",
        default="d4j_validator.csv",
    )
    args = parser.parse_args()


    if args.mode == "checkout":
        bugs = checkout_all_bugs(args.bugs_dir, BENCHMARKS_LIST)
    elif args.mode == 'init':
        bug_dirs = [
            os.path.abspath(dir)
            for dir in glob.glob(f"{args.bugs_dir}/*_*")
            if os.path.isdir(dir) and os.path.exists(f"{dir}/defects4j.build.properties")
        ]

        targets = [
            os.path.basename(dir) for dir in bug_dirs
        ]

        init_bugs(args.bugs_dir, targets, exclude=args.exclude)
    else:
        if args.target != None:
            targets = [
                bug_id
                for bug_id in BENCHMARKS_LIST
                if bug_id in Path(args.target).read_text().strip().split()
            ]
        elif args.all:
            targets = BENCHMARKS_LIST
        else:
            targets = main_target_bugs()
        bugs = init_bugs(args.bugs_dir, targets, args.exclude)

    if args.mode == "d4j-build":
        build_defects4j_projects(bugs)

    elif args.mode == "gzoltar":
        utils.multiprocess(Bug.gzoltar, bugs, n_cpus=10)

    elif args.mode == "capture":
        capture_all_bugs(bugs)

    elif args.mode == "preanal":
        log_pre = open("d4j.preanal.log", "w")
        log_pre.close()
        utils.multiprocess(preanal, bugs, n_cpus=4)

    elif args.mode == "analyze_bug_only":
        msg = (
            "============ start to analyze at "
            + str(time.strftime("%m%d_%I%M", time.localtime()))
            + "================="
        )
        # slack.chat.post_message(channel="slack-analyze", text=msg)
        analyze_bugs_only(bugs, pfl=args.pfl,
                          exnchecker=args.exnchecker, no_test=args.no_test)
        setting = "exnchecker" if args.exnchecker else ""
        filename = evaluate(bugs, setting + args.setting)
        # slack.files.upload(filename, channels="slack-analyze")

    elif args.mode == "evaluate":
        # evaluate(bugs, args.setting)
        evaluate_ap(bugs, args.setting)

    elif args.mode == "tracer":
        targets = [tracer.Target(bug.project_root_dir) for bug in bugs]
        multiprocess_with_logging_result(
            logpath="d4j.tracer.log",
            num_processes=16,
            task=partial(tracer.Target.run, timeout=600),
            args=targets,
        )

    elif args.mode == "enum-ap":
        if args.setting:
            date = args.setting
        else:
            date = time.strftime("%Y-%m-%d")

        def synthesis(mode):
            fl_tag = "pfl" if args.pfl else "sbfl"
            name = f"ap_{date}_{fl_tag}_{mode}"
            session_dir = f"{ROOT_DIR}/abstractPatches/{name}"
            utils.make_dir_if_not_exists(f"{ROOT_DIR}/abstractPatches")
            utils.make_dir_if_not_exists(session_dir)
            utils.execute(f"rm -r */convert_ir_patches.json", dir=args.bugs_dir)
            multiprocess_with_logging_result(
                logpath=f"{session_dir}/d4j.abspatch.{name}.log",
                num_processes=16,
                task=partial(Bug.synthesis, mode=mode, pfl=args.pfl),
                args=bugs,
            )
            utils.execute(
                f"cp --parents */convert_ir_patches.json {session_dir}/",
                dir=args.bugs_dir,
            )
            return session_dir

        if args.prune_mode == "all":
            # synthesis("baseline")
            session_dir = synthesis("template")
            evaluate(bugs, args.setting, output_dir=session_dir)
        else:
            session_dir = synthesis(args.prune_mode)
            evaluate(bugs, args.setting, output_dir=session_dir)

    elif args.mode == "enum-concrete":
        if args.setting:
            date = args.setting
        else:
            date = time.strftime("%Y-%m-%d")

        def enumerate(mode):
            task = partial(Bug.enumerate, mode=mode)
            name = f"enum_{date}_{mode}"
            utils.execute(f"rm -r */patches*", dir=ROOT_DIR)
            multiprocess_with_logging_result(
                logpath=f"d4j.concrete.{name}_{mode}.log",
                num_processes=16,
                task=task,
                args=bugs,
            )
            utils.make_dir_if_not_exists(f"{ROOT_DIR}/concretePatches")
            utils.make_dir_if_not_exists(f"{ROOT_DIR}/concretePatches/{name}")
            utils.execute(
                f"cp --parents */patches.json concretePatches/{name}/", dir=ROOT_DIR
            )

        if args.prune_mode == "all":
            # enumerate("baseline")
            enumerate("template")
            evaluate_ap(bugs, date)

        else:
            enumerate(args.prune_mode)

    elif args.mode == "utils":
        multiprocess_with_logging_result(
            logpath=f"d4j.localize.log",
            num_processes=8,
            task=Bug.gzoltar,
            args=bugs,
        )
