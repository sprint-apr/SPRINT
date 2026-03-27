from multiprocessing import Pool
import logging
import os
import time, datetime
import shutil

import tqdm
import utils
from config import *
import glob
import argparse
from functools import partial

BENCHMARKS_LIST = [bug_id.replace("\n", "") for bug_id in open(
    f'{SCRIPT_DIR}/target.lst', 'r').readlines()]

def multiprocess_with_logging_result(logpath, num_processes, task, args):
    print(args)
    with open(logpath, 'w') as f:
        f.write(f'# execution time: {time.strftime("%Y-%m-%d %H:%M")}\n')
        with Pool(processes=num_processes) as p:
            for result in tqdm.tqdm(p.imap_unordered(task, args), total=len(args)):
                time.sleep(0.5)
                logging.info("Result: %s", result)
                print(result)
                f.write(result + '\n')
                f.flush()
        p.close()
        p.join()


def run(self, timeout=18000, verbose=False):
    if os.path.isdir(f"{self.project_root_dir}/patches"):
        shutil.rmtree(f"{self.project_root_dir}/patches")
    start_time = time.time()
    patch_id = 0
    for patch in self.patches:
        patch_id += 1
        if int(time.time() - start_time) > timeout:
            break
        result = self.validate(patch, patch_id)
        print(f" - validation result for {self.id}-{patch_id}: {result}")



def run_validate(result_path, timeout, d):
    bug_dir = d['bug_dir']
    patches_json_path = d['patches_json_path']
    ret = utils.execute(
        f"python3 {SCRIPT_DIR}/validator.py {bug_dir} {patches_json_path} {timeout} {result_path}", timeout=timeout, dir=bug_dir)
    logging.info(f"Running validation for {bug_dir} with patches {patches_json_path}")
    bug_id = os.path.basename(bug_dir).replace("_", " ")
    if ret.return_code == 0:
        result = "PLAUSIBLE_FOUND"
    elif ret.return_code == 254:
        result = "NO_PATCHES"
    elif ret.return_code == 255:
        result = "TIMEOUT"
    else:
        result = "ERROR"

    msg = f"{bug_id}, {ret.time}, {result}"
    with open(patches_json_path.replace('.json', '.log'), 'w') as f:
        f.write(datetime.datetime.now().strftime('%m%d-%H%M') + '\n')
        f.write(msg + '\n')
        f.write('========= STDOUT ===========' + '\n')
        f.write(ret.stderr + '\n')
        f.write('========= STDERR ===========' + '\n')
        f.write(ret.stderr)

    return msg


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "bugs_dir", help="directory containing bugs checked-out from D4J")
    parser.add_argument(
        "patches_dir", help='[SETTING] in [SETTING]/[BUG_ID]/patches.json')
    parser.add_argument("--timeout", default=18000)
    parser.add_argument("--ncpus", default=10)
    args = parser.parse_args()
    date = datetime.datetime.now().strftime('%m%d-%H%M')
    bugs_dir = [os.path.abspath(dir) for dir in glob.glob(
        f'{args.bugs_dir}/*_*') if os.path.isdir(dir) and os.path.basename(dir) in BENCHMARKS_LIST] 

    patches_json_paths = glob.glob(f"{args.patches_dir}/*/patches.json")
    trial_id = os.path.basename(os.path.abspath(
        args.patches_dir)).split('.patches')[0]

    tasks = []
    for patch_json in patches_json_paths:
        bug_id = patch_json.split('/')[-2]
        bug_dir = args.bugs_dir + '/' + bug_id
        tasks.append({
            'bug_dir': os.path.abspath(bug_dir),
            'patches_json_path': os.path.abspath(patch_json)
        })

    result_path = os.path.abspath(f"{args.bugs_dir}/{trial_id}-time.csv")
    open(result_path, 'w').close()

    multiprocess_with_logging_result(logpath=f"{trial_id}-{args.timeout}.csv",
                                     num_processes=int(args.ncpus),
                                     task=partial(run_validate, result_path,
                                                  int(args.timeout)),
                                     args=tasks)
