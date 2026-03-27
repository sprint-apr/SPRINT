#!/usr/bin/python3.8
import argparse
import time
import os
import shutil
import utils
from dataclasses import asdict, dataclass
from config import *
from bug import Bug
import tracer

ROOT_DIR = os.getcwd()


@dataclass
class Result:
    compile_time: float = 0.0
    is_compiled: bool = False
    preanal_time: float = 0.0
    is_preanal: bool = False
    analyze_time: float = 0.0
    number_of_abs_patches: int = 0
    number_of_weak_accepted_abs_patches: int = 0
    number_of_accepted_abs_patches: int = 0

    def from_json(bug_dir):
        if os.path.isfile(f"{bug_dir}/results.json") is False:
            return Result()
        dict = utils.read_json_from_file(f"{bug_dir}/results.json")
        return utils.from_dict(Result, dict)

    def to_json(self, bug_dir):
        utils.save_dict_to_jsonfile(f"{bug_dir}/results.json", asdict(self))


def do_prepare(bug, args):
    if args != None:
        if args.build_only:
            bug.d4j_build()
            return

        if args.capture_only:
            bug.capture_all(True)
            return

    bug.d4j_build()
    bug = Bug(bug.project_root_dir)
    bug.capture_all(True)
    return Bug(bug.project_root_dir)


def do_trace(bug, args):
    tracer.Target(bug.root).run(1200, verbose=True)


def do_analyze(bug, args):
    if not args.skip_preanal and not args.main_only and not args.exn_only:
        bug.preanal(args.debug)

    if args.pre_only:
        return

    if args.exn_only or args.main_only:
        bug.analyze(args.debug, args.pfl, args.pool,
                    args.exn_only, args.no_test, args.flonly)
        return

    bug.analyze(args.debug, args.pfl, args.pool,
                True, args.no_test, args.flonly)
    bug.analyze(args.debug, args.pfl, args.pool,
                False, args.no_test, args.flonly)


def do_enum_ap(bug, args):
    bug.synthesis(args.prune_mode, pfl=args.pfl)


def do_localize(bug, args):
    bug.gzoltar(verbosity=True)


def do_logging(bug, args):
    bug.logging(args)


def do_synthesis(bug, args):
    bug.enumerate(args.prune_mode)


if __name__ == "__main__":
    bug = Bug(ROOT_DIR)

    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="mode", help="mode")
    parser.add_argument(
        "--cpus", default=int(os.cpu_count() / 2), help="number of cpus"
    )
    parser.add_argument(
        "--no-test",
        default=False,
        action="store_true",
        help="run analysis without test information",
    )

    # Localize mode
    localize = subparsers.add_parser(
        "localize", help="(Optional) localize abs_patches by SBFL ochiai")
    localize.set_defaults(func=do_localize)

    # Localize mode
    logging = subparsers.add_parser(
        "logging", help="logging stack trace for specified path and line")
    logging.set_defaults(func=do_logging)
    logging.add_argument("path", help="file path")
    logging.add_argument("line", help="line number")
    logging.add_argument(
        "--output", help="output filename", default="test.log")

    # Prepare mode
    prepare = subparsers.add_parser(
        "prepare", help="Step 1: prepare D4J bug to repair")
    prepare.set_defaults(func=do_prepare)
    prepare.add_argument(
        "--build-only",
        default=False,
        action="store_true",
        help="prepare D4J bug and check if the test fails properly",
    )
    prepare.add_argument(
        "--capture-only",
        default=False,
        action="store_true",
        help="capture the buggy project by Infer's frontend",
    )

    # Tracer mode
    trace = subparsers.add_parser("trace", help="Step 2: run tracer")
    trace.set_defaults(func=do_trace)

    # Analysis mode
    analysis = subparsers.add_parser("analyze", help="run sprint analysis")
    analysis.set_defaults(func=do_analyze)
    analysis.add_argument("--pool", default=-1,
                          help="specify infer CPU pool number")
    analysis.add_argument(
        "--pre-only", default=False, action="store_true", help="run pre-analysis"
    )
    analysis.add_argument(
        "--main-only",
        default=False,
        action="store_true",
        help="run main analysis only",
    )
    analysis.add_argument(
        "--exn-only",
        default=False,
        action="store_true",
        help="run exception checker only",
    )
    analysis.add_argument(
        "--pfl",
        default=False,
        action="store_true",
        help="run analysis under the perfect fault localization (PFL) setting",
    )
    analysis.add_argument(
        "--flonly",
        default=False,
        action="store_true",
        help="run analysis with dropped ochiai result (for debugging purpose)",
    )
    analysis.add_argument("--debug", default=False, help="debug option")
    analysis.add_argument("--skip-preanal", default=False,
                          action="store_true", help="skip preanalysis")

    # Enum-ap mode
    enum_ap = subparsers.add_parser(
        "enum-ap", help="enumerate pruned templates")
    enum_ap.set_defaults(func=do_enum_ap)
    enum_ap.add_argument(
        "--prune_mode",
        help="mode to run FL",
        default="template",
        choices=["template", "baseline", "line", "all"],
    )
    enum_ap.add_argument(
        "--pfl",
        default=False,
        action="store_true",
        help="enumerate aps under the perfect fault localization (PFL) setting",
    )

    # Synthesis mode
    synthesis = subparsers.add_parser("synthesis")
    synthesis.set_defaults(func=do_synthesis)
    synthesis.add_argument(
        "--prune_mode",
        help="mode to run FL",
        default="template",
        choices=["template", "baseline", "line", "all"],
    )
    args = parser.parse_args()
    if args.mode != None:
        args.func(bug, args)
        exit(0)

    start_time = time.time()
    bug = do_prepare(bug, None)
    do_trace(bug, None)
    bug.preanal(False)
    bug.analyze(debug=False, pfl=False, pool=-1,
                exnchecker=True, no_test=args.no_test)
    bug.analyze(debug=False, pfl=False, pool=-1,
                exnchecker=False, no_test=args.no_test)
    bug.synthesis("template")
    time_to_fl = time.time() - start_time
    print(f"{bug.id}, {time_to_fl}")
    exit(0)
