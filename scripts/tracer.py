import glob
import re
from typing import List
import utils
from bug import Bug
from config import *
import os

class Target(Bug):
    class_path: str
    test_classes: List[str]

    def __init__(self, project_root_dir):
        super().__init__(project_root_dir)
        with open(f"{project_root_dir}/.classpath.d4j") as f:
            self.class_path = f.readlines()[0]

        self.test_classes = list(
            set([re.sub("::.*", "", m.strip()) for m in self.test_methods])
        )

    def run(self, timeout, verbose=False):
        env = os.environ.copy()
        env['TZ'] = 'America/Los_Angeles'
        jvm_opts = "-Xms128m -Xmx128m" if self.id == "Lang_43" else ""
        test_methods = [t.replace("::", "#") for t in self.test_methods]

        for test_class in self.test_classes:
            test_methods_within_class = [
                t for t in test_methods if t.startswith(test_class)
            ]
            cmd = (
                f'java {jvm_opts} -javaagent:{AGENT_JAR_PATH}=".,{test_class}" '
                f"-cp {JUNIT_CLASSPATH}:{self.sprint_classes_dir}:{self.class_path} "
                f'{JUNIT_CORE_CLASS} {",".join(test_methods_within_class)}'
            )

            if verbose:
                print(cmd)

            ret = utils.execute(
                cmd, dir=self.project_root_dir, verbosity=0, timeout=timeout, env=env
            )

        succeed = True
        for tc in self.test_classes:
            if os.path.isfile(f"{self.project_root_dir}/sprint-out/{tc}/InvokedWell.csv") is False:
                succeed = False
                break

            with open(f"{self.project_root_dir}/sprint-out/{tc}/InvokedWell.csv", 'r') as fp:
                line = fp.readline().strip('\n')
                if not line.endswith("false") and not line.endswith("true"):
                    succeed = False
                    break

        if succeed:
            log = f"{SUCCESS}: {self.id},{ret.return_code},{ret.time}"
        else:
            log = f"{FAIL}: {self.id},{ret.return_code},{ret.time}"
        
        if verbose:
            print(log) 
        return log


if __name__ == "__main__":
    Target(".").run(3600, verbose=True)
