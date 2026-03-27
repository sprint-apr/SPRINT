#!/usr/bin/python3.9

from functools import partial
import concurrent.futures
import os
import sqlite3
import time
from dataclasses import dataclass, asdict
from enum import Enum, auto
from typing import List, Optional
from pathlib import Path
import shutil
import sys

import utils
import hashlib
from config import *
import config
import json


@dataclass
class Patch:
    source_path: str
    bug_id: str
    line_from: int
    line_to: int
    patch_code: str

    def key(self):
        patch_code = "".join(self.patch_code.split())
        return f"{self.bug_id}@,{self.source_path}@,{self.line_from},{self.line_to}@,{patch_code}"

    def create_source(self, project_root_dir, patch_id):
        basename = os.path.basename(self.source_path)
        dirname = f"{project_root_dir}/patches/{patch_id}"
        utils.make_dir_if_not_exists(f"{project_root_dir}/patches")
        utils.make_dir_if_not_exists(dirname)

        try:
            with open(f"{project_root_dir}/{self.source_path}", 'r') as org_file:
                lines = org_file.readlines()
        except:
            with open(f"{project_root_dir}/{self.source_path}", 'r', encoding='ISO-8859-1') as org_file:
                lines = org_file.readlines()

        pre_line = "".join(lines[:self.line_from - 1])
        post_line = "".join(lines[self.line_to:])
        self.org_code = "".join(lines[self.line_from -1:self.line_to]).replace(r'\r','')

        with open(f"{dirname}/{basename}", 'w') as patch_file:
            patch_file.write(pre_line + self.patch_code + "\n" + post_line)

        return f"{dirname}/{basename}"
 
    def to_diff(self, project_root_dir, patch_id):
        with open(f"{project_root_dir}/buggy.java", 'w') as f:
            f.write(self.org_code)
        with open(f"{project_root_dir}/patch.java", 'w') as f:
            f.write(self.patch_code)
        ret = utils.execute(f"git diff --no-index buggy.java patch.java", dir=project_root_dir)
        result = "\n".join(ret.stdout.split("\n")[5:-2])
        result = f"{self.source_path}:{self.line_from}~{self.line_to}\n{result}\n"
        with open(f"{project_root_dir}/patch.diff", 'w') as f:
            f.write(result)
        return result 

class ValidationFlag(Enum):
    PLAUSIBLE_FOUND = auto()
    COMPILATION_FAILURE = auto()
    FAILING_TEST_NOT_PASSED = auto()
    REGRESSION_FAILED = auto()
    PARTIAL_PASSED = auto()
    TIMEOUT = auto()


def get_class_path(patch_path):
    return "/".join(patch_path.split("/")[:-1])


@dataclass
class ValidationResult:
    flag: ValidationFlag = None
    compilation_time: int = 0.0
    failing_test_time: int = 0.0
    regression_test_time: int = 0.0
    tests_passed: str = ""


def parseTestResults(test_results_str):
    test_failed = []
    switch = False
    for failing_str in test_results_str.split("\n"):
        if "Runned tests until failure" in failing_str:
            switch = True
            continue
        if not switch or failing_str == "":
            continue

        parts = failing_str.split('(')
        method_name = parts[0].strip()
        class_name = parts[1].strip().strip(')')
        test_failed.append(f"{class_name}#{method_name}")
    return test_failed


class Target:
    id: str
    project_root_dir: str
    root: Path
    classpath: str
    result_path: str
    failing_test_methods: List[str]
    regression_test_classes: List[str]
    patches: List[Patch]

    def __init__(self, project_root_dir, patches_json_path, result_path):
        self.id = os.path.basename(project_root_dir)
        self.project_root_dir = project_root_dir
        self.root = Path(self.project_root_dir)
        self.classpath = (self.root / D4J_CLASSPATH_FILE_NAME).read_text()
        self.result_path = result_path

        with open(f"{project_root_dir}/defects4j.build.properties", 'r') as f:
            test_methods = f.readlines()[-1].split('=')[1].split(',')
        self.failing_test_methods = [
            m.strip().replace('::', '#') for m in test_methods]

        self.regression_test_classes = (
            self.root/D4J_ALL_TESTS_FILE_NAME).read_text().strip().split('\n')

        patches_dict = utils.read_json_from_file(patches_json_path)
        if patches_dict == []:
            exit(-2)
            #raise Exception("empty patches")

        self.patches = [utils.from_dict(Patch, patch_dict)
                        for patch_dict in patches_dict]

    def run_cmd(self, cmd):
        env = os.environ.copy()
        env['TZ'] = 'America/Los_Angeles'
        return utils.execute(f'ID={self.id} {cmd}', dir=self.project_root_dir, env=env)

    def build_java_run_cmd(self, test_args, patch_path, timeout):
        return f'timeout {timeout}s java -cp {JUNIT_CLASSPATH}:{get_class_path(patch_path)}:{self.classpath} {JUNIT_CORE_CLASS} {test_args}'

    def compile(self, patch_path):
        return self.run_cmd(f'javac -cp {self.classpath} {patch_path} -d {get_class_path(patch_path)}')

    def run_failing_tests(self, patch_path):
        failing_test_cmd = self.build_java_run_cmd(
            ','.join(self.failing_test_methods), patch_path, timeout=60)
        return self.run_cmd(failing_test_cmd)

    def run_single_test_class(self, patch_path, failing_test_methods, classname):
        ret = self.run_cmd(self.build_java_run_cmd(
            classname, patch_path, timeout=60))
        # timeout case
        if ret.return_code == 124:
            raise concurrent.futures.process.BrokenProcessPool(
                f"Testing Failure Found: {classname}")

        if ret.return_code != 0:
            tests_failed = parseTestResults(ret.stdout)
            if any([test_failed not in failing_test_methods for test_failed in tests_failed]):
                raise concurrent.futures.process.BrokenProcessPool(
                    f"Testing Failure Found: {classname}")

    def run_regression_tests(self, patch_path, failing_test_methods):
        initial_time = time.time()
        with concurrent.futures.ProcessPoolExecutor(max_workers=8) as executor:
            try:
                list(executor.map(
                    partial(self.run_single_test_class, patch_path, failing_test_methods), self.regression_test_classes))
            except Exception as e:
                return (False, time.time() - initial_time)
        return (True, time.time() - initial_time)

    def save_validation_result(self, conn, key, validation_result):
        cursor = conn.cursor()
        data = asdict(validation_result)
        data["hash"] = (hashlib.sha256(key.encode())).hexdigest()
        data["key_text"] = key
        data["flag"] = data["flag"].name

        cursor.execute(f"""
            REPLACE INTO {self.id} (hash, key_text, flag, compilation_time, failing_test_time, regression_test_time, tests_passed)
            VALUES (:hash, :key_text, :flag, :compilation_time, :failing_test_time, :regression_test_time, :tests_passed)
        """, data)
        conn.commit()

    def load_validation_results(self, conn, key_text) -> Optional[ValidationResult]:
        cursor = conn.cursor()
        key = (hashlib.sha256(key_text.encode())).hexdigest()
        cursor.execute(
            f"SELECT * FROM {self.id} WHERE hash = ?", (key,))
        row = cursor.fetchall()

        if len(row) == 0:
            return None

        row = (list(row))[0]
        return ValidationResult(
            flag=ValidationFlag[row[3]],
            compilation_time=row[4],
            failing_test_time=row[5],
            regression_test_time=row[6],
            tests_passed=row[7]
        )

    def validate(self, conn, patch, patch_id):
        key = patch.key()
        patch_path = patch.create_source(self.project_root_dir, patch_id)

        result = self.load_validation_results(conn, key)
        if result:
            return result

        # compile
        ret_compile = self.compile(patch_path)
        if ret_compile.return_code != 0:
            result = ValidationResult(
                ValidationFlag.COMPILATION_FAILURE, ret_compile.time)
            self.save_validation_result(conn, key, result)
            return result

        # test
        ret_faiiling_test = self.run_failing_tests(patch_path)
        if ret_faiiling_test.return_code == 124:
            test_failed = self.failing_test_methods
        else:
            test_failed = parseTestResults(ret_faiiling_test.stdout)

        tests_passed = list(set(self.failing_test_methods) - set(test_failed))
        if tests_passed == []:
            result = ValidationResult(ValidationFlag.FAILING_TEST_NOT_PASSED,
                                      ret_compile.time, ret_faiiling_test.time)
            self.save_validation_result(conn, key, result)
            return result

        # regression
        tests_passed = "@".join(sorted(tests_passed))
        if test_failed == []:
            reg_result, reg_time = self.run_regression_tests(
                patch_path, self.failing_test_methods)
            if reg_result:
                reg_flag = ValidationFlag.PLAUSIBLE_FOUND
            else:
                reg_flag = ValidationFlag.REGRESSION_FAILED
        else:
            reg_time = 0.0
            reg_flag = ValidationFlag.PARTIAL_PASSED

        result = ValidationResult(reg_flag, ret_compile.time,
                                  ret_faiiling_test.time, reg_time, tests_passed)
        self.save_validation_result(conn, key, result)
        return result

    def record_time(self, time):
        with open(self.result_path, 'a') as f:
            f.write(f"{self.id}, {time}\n")

    def run(self, conn, timeout=18000, verbose=False):
        if os.path.isdir(f"{self.project_root_dir}/patches"):
            shutil.rmtree(f"{self.project_root_dir}/patches")

        elapsed_time = 0.0
        patch_id = 0
        partial = 0
        plausible_found = False
        compile_time = 0.0
        failing_test_time = 0.0
        regression_test_time = 0.0
        plausible_patches = []
        for patch in self.patches:
            patch_id += 1

            if elapsed_time > float(timeout):  # Timeout
                if not plausible_found:
                    print(f"{TIMEOUT} to validate {patch_id} patches for {self.id}")
                    print(f" - compilation time : {compile_time}")
                    print(f" - failing test time : {failing_test_time}")
                    print(f" - regression test time : {regression_test_time}")
                else:
                    print(plausible_found)
                    print(f"partial patches {partial}")
                break

            result = self.validate(conn, patch, patch_id)
            if result is None:
                break

            print(f"[{patch_id}/{len(self.patches)}] {result} (Patched line-from: {patch.line_from})")


            compile_time += result.compilation_time
            failing_test_time += result.failing_test_time
            if len(result.tests_passed) != len(self.failing_test_methods):
                if result.tests_passed != "" and not plausible_found:
                    partial += 1
                elapsed_time += result.compilation_time + \
                    result.failing_test_time
            else:
                elapsed_time += result.compilation_time + \
                    result.failing_test_time + result.regression_test_time
                regression_test_time += result.regression_test_time

            if not plausible_found and result.flag == ValidationFlag.PLAUSIBLE_FOUND:
                plausible_patches.append(patch)
                plausible_found = True
                plausible_found = f"{SUCCESS} found plausible patches {elapsed_time}\n{patch}"
                # print(f"{SUCCESS} found plausible patches {elapsed_time}")
                # print(patch)
                self.record_time(elapsed_time)
            elif result.flag == ValidationFlag.PLAUSIBLE_FOUND:
                plausible_patches.append(patch)
                plausible_found = f"{plausible_found}\n---------------------------------\n{patch}"
                print(plausible_found)

        if plausible_patches != []:
            with open(f"{self.project_root_dir}/plausible_patches_{self.id}.json", 'w') as f:
                patches_dict = [asdict(patch) for patch in plausible_patches]
                f.write(json.dumps(patches_dict, indent=4))

        # Timeout
        if not plausible_found and elapsed_time > float(timeout):
            print(f"{FAIL} timeout for {self.id}")
            print(f" - compilation time : {compile_time}")
            print(f" - failing test time : {failing_test_time}")
            print(f" - regression test time : {regression_test_time}")
            return -1

        # No Patches
        if not plausible_found:
            print(f"{FAIL} no plausible patch found for {self.id}")
            print(f" - compilation time : {compile_time}")
            print(f" - failing test time : {failing_test_time}")
            print(f" - regression test time : {regression_test_time}")
            return -2

        # Plausible found
        print(plausible_found)
        print(f"partial patches {partial}")
        return 0


if __name__ == '__main__':
    if len(sys.argv) < 3:
        print(f"{ERROR}: bug-directory and patches.json not given", file=sys.stderr)
        print(
            "Usage: [bug_dir] [patches.json] Optional[timeout] Optional[res.csv]")
        sys.exit(1)

    timeout = 18000 if len(sys.argv) == 3 else int(sys.argv[3])

    bug_dir = os.path.abspath(sys.argv[1])
    patches_json_path = os.path.abspath(sys.argv[2])

    result_path = os.path.abspath(sys.argv[4]) if len(
        sys.argv) == 5 else os.path.abspath("res.csv")

    conn = sqlite3.connect(config.VALIDATION_DB_PATH)
    try:
        target = Target(bug_dir, patches_json_path, result_path)
        cursor = conn.cursor()
        cursor.execute(f"""
            CREATE TABLE IF NOT EXISTS {target.id} (
                id INT AUTO_INCREMENT PRIMARY KEY,
                hash VARCHAR(255) UNIQUE,
                key_text TEXT,
                flag TEXT,
                compilation_time DOUBLE,
                failing_test_time DOUBLE,
                regression_test_time DOUBLE,
                tests_passed TEXT
            )
        """)

        conn.commit()
        sys.exit(target.run(conn=conn, timeout=timeout, verbose=True))
    except Exception as e:
        print(e, file=sys.stderr)
        sys.exit(1)
