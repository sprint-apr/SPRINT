#!/usr/bin/python3.9

from functools import partial
import utils
import patch
from patch import Patch, ValidationFlag
from bug import Bug
from config import D4J_CLASSPATH_FILE_NAME, D4J_ALL_TESTS_FILE_NAME, JUNIT_CLASSPATH, JUNIT_CORE_CLASS
from multiprocessing import Pool
import os
import time
import json
import pandas as pd


class Target(Bug):
    result_headers = ['BUG_ID', 'IR_PATCHES', 'PRUNED', 'SOURCE_PATCHES', 'COMPILATION_TIME',
                      'FAILING_TEST_TIME', 'REGRESSION_TEST_TIME'] + [f.name for f in ValidationFlag]

    def __init__(self, project_root_dir):
        super().__init__(project_root_dir)
        self.classpath = (self.root / D4J_CLASSPATH_FILE_NAME).read_text()
        self.synthesis_result_json = self.root / 'convert_ir_patches.json'
        self.failing_test_methods = [m.strip().replace('::', '#') for m in self.test_methods]
        self.regression_test_classes = (self.root/D4J_ALL_TESTS_FILE_NAME).read_text().strip().split('\n')
        self.validation_result_json = self.root / 'validation_result.python.json'
        self.summary_csv = self.root / 'validation_summary.csv'

    class Decorator:
        @classmethod
        def update_elapsed_time(cls, varname):
            def deco(func):
                def inner(*args, **kwargs):
                    t_begin = time.time()
                    result = func(*args, **kwargs)
                    args[1].__dict__['validation_result'].__dict__[varname] = time.time() - t_begin
                    return result
                return inner
            return deco

    def run_cmd(self, cmd):
        env = os.environ.copy()
        env['TZ'] = 'America/Los_Angeles'
        return utils.execute(f'ID={self.id} {cmd}', dir=self.project_root_dir, env=env)

    def build_java_run_cmd(self, test_args, patch, timeout):
        return f'timeout {timeout}s java -cp {JUNIT_CLASSPATH}:{patch.get_patch_class_path()}:{self.classpath} {JUNIT_CORE_CLASS} {test_args}'

    @Decorator.update_elapsed_time('compilation_time')
    def compile(self, patch):
        return self.run_cmd(
            f'javac -cp {self.classpath} {patch.rewriting_result.source_path} -d {patch.get_patch_class_path()}')

    @Decorator.update_elapsed_time('failing_test_time')
    def run_failing_tests(self, patch):
        failing_test_cmd = self.build_java_run_cmd(','.join(self.failing_test_methods), patch, timeout=60)
        return self.run_cmd(failing_test_cmd)

    def run_single_test_class(self, patch, classname):
        ret = self.run_cmd(self.build_java_run_cmd(classname, patch, timeout=60))
        if ret.return_code != 0:
            raise Exception(f"Testing Failure Found: {classname}")

    @Decorator.update_elapsed_time('regression_test_time')
    def run_regression_tests(self, patch):
        with Pool(processes=8) as pool:
            try:
                list(pool.imap_unordered(
                    partial(self.run_single_test_class, patch), self.regression_test_classes))
            except Exception:
                return ValidationFlag.REGRESSION_FAILED
        return ValidationFlag.PLAUSIBLE_FOUND

    def summarize_result(self):
        patches = utils.read_json_from_file(self.validation_result_json)
        d = dict.fromkeys(Target.result_headers, 0)
        d['BUG_ID'] = self.id
        d['IR_PATCHES'] = len(patches)
        d['PRUNED'] = len([p for p in patches if p['pruning_result'] == 'SAT'])
        d['SOURCE_PATCHES'] = len([p for p in patches if (r := p['rewriting_result']) != None and r['succeed']])
        for p in patches:
            if (r := p['validation_result']) is None:
                continue
            d['COMPILATION_TIME'] += r['compilation_time']
            d['FAILING_TEST_TIME'] += r['failing_test_time']
            d['REGRESSION_TEST_TIME'] += r['regression_test_time']
            d[r['flag']] += 1
        return pd.Series(d).to_frame().T.set_index('BUG_ID')

    def run(self, timeout=10800, verbose=False):
        initial_time = time.time()
        patches = patch.from_ocaml_result_json(self.synthesis_result_json)
        try:
            converted_patches = [p for p in patches if p.is_converted()]
            for p in converted_patches:
                elapsed_time = time.time() - initial_time
                p.validation_result = Patch.ValidationResult(elapsed_time)
                if elapsed_time > timeout:
                    p.validation_result.flag = ValidationFlag.TIMEOUT
                    continue
                else:
                    if self.compile(p).return_code != 0:
                        flag = ValidationFlag.COMPILATION_FAILURE
                    elif self.run_failing_tests(p).return_code != 0:
                        flag = ValidationFlag.FAILING_TEST_NOT_PASSED
                    else:
                        flag = self.run_regression_tests(p)

                    p.validation_result.flag = flag
                    if verbose:
                        print(f'{p.get_patch_source_path()}: {p.validation_result.flag}')
        except Exception:
            print(f'Someting goes wrong with validating {self.id}')
        finally:
            with open(self.validation_result_json, 'w') as f:
                json.dump([p.asdict() for p in patches], fp=f, indent=4)
            (summary := self.summarize_result()).to_csv(self.summary_csv)
            return summary


if __name__ == '__main__':
    Target('.').run(verbose=True)
