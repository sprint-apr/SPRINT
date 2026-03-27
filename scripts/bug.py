import fcntl
import os
import pathlib
import re
import shutil
import random
import time
import subprocess
import glob
import utils
import gzoltar
from pathlib import Path
from config import *
import multiprocessing
import xml.etree.ElementTree as ET
import ochiai

def jar_name(path):
    if ".jar" not in path:
        return path
    
    basename = os.path.basename(path)
    return basename.split("-")[0]


class Bug:
    project_root_dir: str
    id: str
    project_name: str
    build_type: str
    class_path: str
    sprint_classes_dir: str
    test_methods: str
    time_to_analyze: float
    time_to_capture: float
    java_version_file: str
    java_version: str = None
    ant_version: str
    opt: str

    VALIDATION_RESULTS_NAME: str = "feasible_abs_patches"
    ALL_TESTS_FILE_NAME: str = "defects4j.tests.all"
    SYNTHESIS_STATUS_NAME: str = "overall_status.json"

    @staticmethod
    def init_cppath(project_root_dir, project_name):
        cppath = f"{project_root_dir}/.classpath.d4j"
        print(f"{PROGRESS}: init cp {cppath}...")
        export_cmd = f"{DEFECTS4J} export -p cp.test -w {project_root_dir}"
        cp_exported = subprocess.run(export_cmd,
                                        shell=True,
                                        capture_output=True).stdout.decode()

        with open(cppath, "w") as f:
            # Add common dependencies specified by D4J
            common_libs = []
            if project_name == "Mockito":
                common_libs += [
                    os.path.abspath(jar) for jar in glob.glob(
                        f"{project_root_dir}/lib/**/*.jar", recursive=True)
                ]
            if os.path.exists(f"{project_root_dir}/maven-build.xml"):
                with open(f"{project_root_dir}/maven-build.xml",
                            "r") as xml_file:
                    xml_data = xml_file.read()
                root = ET.fromstring(xml_data)
                build_test_classpath = root.find(
                    ".//path[@id='build.test.classpath']")
                locations = build_test_classpath.findall(
                    "pathelement[@location]")
                location_values = [
                    location.get("location") for location in locations
                ]
                location_values = [
                    "/".join(location.split("/")[1:])
                    for location in location_values
                ]
                common_libs += [
                    f"{D4J_HOME}/framework/projects/{project_name}/lib/{jarpath}"
                    for jarpath in location_values
                ]
            else:
                common_libs += [
                    os.path.abspath(jar) for jar in glob.glob(
                        f"{D4J_HOME}/framework/projects/{project_name}/lib/**/*.jar",
                        recursive=True,
                    )
                ]

            # Exclude Junit versions below 4.11 for compatibility with Gzoltar
            common_libs = [lib for lib in common_libs if not is_junit_below_4_11(lib)]
            common_libs.append(
                f"{D4J_HOME}/framework/projects/lib/junit-4.11.jar")
            common_libs.append(
                f"{D4J_HOME}/framework/projects/lib/cobertura-2.0.3.jar")

            # remove duplicated and invalid classpaths
            cp_added = set()
            cp_exported = [
                cp for cp in cp_exported.split(":")
                if "${" not in cp and jar_name(cp) not in cp_added and not cp_added.add(jar_name(cp))
            ]

            cp_exported = ":".join(cp_exported)

            f.write(":".join(common_libs))
            f.write(":" + cp_exported)

        with open(cppath, "r") as f:
            classpath = f.readline()

        return classpath

    def __init__(self, project_root_dir):
        self.project_root_dir = project_root_dir
        self.root = Path(self.project_root_dir)
        self.id = os.path.basename(project_root_dir)
        self.project_name = self.id.split("_")[0]
        utils.remove_file_if_exists(
            f"{self.project_root_dir}/infer-out/sqlite_write_socket")
        if os.path.isfile(f"{project_root_dir}/defects4j.build.properties"):
            self.build_type = "defects4j"
            self.class_path = Bug.init_cppath(project_root_dir,
                                              self.project_name)
            with open(f"{project_root_dir}/defects4j.build.properties",
                      "r") as f:
                self.test_methods = f.readlines()[-1].split("=")[1].split(",")
            self.java_version_file = f"{project_root_dir}/.java_version.d4j"
            try:
                with open(self.java_version_file, "r") as f:
                    self.java_version = f.readline()
            except FileNotFoundError:
                self.java_version = 1.8

        elif os.path.isfile(f"{project_root_dir}/pom.xml"):
            self.build_type = "mvn"
            self.class_path = None
        else:
            print(
                f"[FAIL] {os.path.basename(project_root_dir)}: unsupported build system"
            )
            exit(1)

        # Additional javac options for each project
        if "Lang_" in os.path.basename(self.project_root_dir) or "Compress_" in os.path.basename(self.project_root_dir):
            # opt = '-encoding ISO-8859-1 -source 1.4'
            self.opt = "-encoding ISO-8859-1"
        else:
            self.opt = ""

        if not os.path.exists(
            all_tests := f"{project_root_dir}/{self.ALL_TESTS_FILE_NAME}"
        ):
            print (f"{PROGRESS}: export all tests to {all_tests} ...")
            utils.execute(
                cmd := f"{DEFECTS4J} export -p tests.all -o {all_tests}",
                dir=self.project_root_dir,
            )
            if not os.path.exists(all_tests):
                print(f"{WARNING} to export all tests for {self.id} (skipping)")

        # Check if ochiai csv properly setup or copy it from resources dir
        if not (ochiai_path := self.root / 'ochiai.txt').exists():
            if os.path.exists(ochiai.filepath(self.id)):
                shutil.copyfile(ochiai.filepath(self.id), ochiai_path)
            else:
                print(f"{WARNING} no ochiai data found for {self.id}")

        self.time_to_analyze = 0.0
        self.time_to_capture = 0.0
        if self.project_name == "Lang":
            self.ant_version = "1.8.4"
        else:
            self.ant_version = "1.10.15"
        self.sprint_classes_dir = f"{project_root_dir}/sprint-classes"

    def from_dir(bug_dir):
        return Bug(bug_dir)

    @classmethod
    def d4j_clone(cls, bug_id, bugs_dir):
        proj, id = bug_id.split("_")
        wdir = f"{bugs_dir}/{bug_id}"
        cmd = f"{DEFECTS4J} checkout -p {proj} -v {id}b -w {wdir}"

        print(cmd)
        if not os.path.isfile(f"{wdir}/defects4j.build.properties"):
            ret = subprocess.run(cmd, shell=True, capture_output=True)
            if ret.returncode != 0:
                print(f"Something goes wrong cloning {bug_id} at {bugs_dir} ({cmd})\n{ret.stderr}\n")
                return None

        if not os.path.isfile(ochiai.filepath(bug_id)):
            print(f"No ochiai data for {bug_id} at {bugs_dir} ({cmd})")
            return None

        shutil.copyfile(
            ochiai.filepath(bug_id),
            f"{wdir}/ochiai.txt",
        )

    ### NOTE: ant.1.10.15 should be prepared in D4J_HOME/major/bin/ant.1.10.15
    ### and, ant.1.8.4 also should be prepared in D4J_HOME/major/bin/ant.1.8.4
    def d4j_test(self):
        # Use older ant for Lang project
        defects4j_ant_path = f"{D4J_HOME}/major/bin/ant"
        ant_with_version = f"{os.path.dirname(defects4j_ant_path)}/ant.{self.ant_version}"
        

        os.environ["JAVA_HOME"] = JDK_8

        # Check if ant version is already correct
        current_version_output = utils.execute(f"{defects4j_ant_path} -version").stdout
        if self.ant_version in current_version_output:
            print(f"build by ant {self.ant_version}", end="")
            ret = utils.execute(f"{DEFECTS4J} test", dir=self.project_root_dir)
            print(f" ... Done!")
        else:
            LOCK_FILE = f"/tmp/ant_cp.lock"
            with open(LOCK_FILE, "w") as lock_file:
                fcntl.flock(lock_file, fcntl.LOCK_EX)

                # secondary version check: another process may have already copied
                current_version_output = utils.execute(f"{defects4j_ant_path} -version").stdout
                if self.ant_version in current_version_output:
                    # version already correct, release lock immediately
                    fcntl.flock(lock_file, fcntl.LOCK_UN)
                else:
                    # perform copy
                    os.remove(defects4j_ant_path)
                    os.system(f"ln -s {ant_with_version} {defects4j_ant_path}")

                    # verify after copy
                    current_version_output = utils.execute(f"{defects4j_ant_path} -version").stdout
                    if self.ant_version not in current_version_output:
                        fcntl.flock(lock_file, fcntl.LOCK_UN)  # release and exit
                        print(f"Failed to set ant version to {self.ant_version}")
                        exit(-1)

                    fcntl.flock(lock_file, fcntl.LOCK_UN)  # release

            print(f"build by ant {self.ant_version}", end="")
            ret = utils.execute(f"{DEFECTS4J} test", dir=self.project_root_dir)
            print(f" ... Done!")

        export_src_cmd = (
            f"{DEFECTS4J} export -p dir.src.classes -w {self.project_root_dir}"
        )
        src_dir = (
            self.project_root_dir
            + "/"
            + utils.execute(export_src_cmd, dir=self.project_root_dir).stdout
        )
        export_testsrc_cmd = (
            f"{DEFECTS4J} export -p dir.src.tests -w {self.project_root_dir}"
        )
        testsrc_dir = (
            self.project_root_dir
            + "/"
            + utils.execute(export_testsrc_cmd,
                            dir=self.project_root_dir).stdout
        )
        java_files = glob.glob(f"{src_dir}/**/*.java", recursive=True) + glob.glob(
            f"{testsrc_dir}/**/*.java", recursive=True
        )
        with open(f"{self.project_root_dir}/java_files", "w") as f:
            java_files_str = "\n".join(java_files)
            f.writelines(java_files_str)

        utils.make_dir_if_not_exists(self.sprint_classes_dir)
        for version in ["1.8", "1.7", "1.6", "1.5", "1.4"]:
            utils.make_dir_if_not_exists(self.sprint_classes_dir)
            build_cmd = f"javac -d {self.sprint_classes_dir} {self.opt} -source {version} -cp {self.class_path} @{self.project_root_dir}/java_files"
            completed = utils.execute(build_cmd, dir=self.project_root_dir)
            if completed.return_code != 0:
                continue

            with open(self.java_version_file, "w") as f:
                f.write(version)
            break

        return ret

    def d4j_build(self):
        ret = self.d4j_test()
        print(ret.stderr)
        print(msg := f"{self.id}, {ret.return_code}\n")
        return msg

    def checkout(self):
        ret = subprocess.run(
            f"git checkout -- {self.project_root_dir}",
            shell=True,
            cwd=self.project_root_dir,
        )
        if ret.returncode == 128:
            backoff = random.uniform(0.1, 2.0)
            time.sleep(backoff)
            self.checkout()

        elif ret.returncode != 0:
            print(f"[FAIL] git checkout")
            exit(-1)

    def capture_all(self, skip_checkout=False):
        start_time = time.time()
        if not skip_checkout:
            self.checkout()

        if self.build_type == "mvn":
            build_cmd = f"mvn clean package {MVN_OPT}"
            capture_cmd = f"{INFER_PATH} capture -- {build_cmd}"
            print(f"[PROGRESS]: capture project by {capture_cmd}")
            completed = utils.execute(capture_cmd, dir=self.project_root_dir)
            self.time_to_capture_original = time.time() - start_time

        elif self.build_type == "defects4j":
            build_cmd = f"javac -d {self.sprint_classes_dir} {self.opt} -source {self.java_version} -cp {self.class_path} @{self.project_root_dir}/java_files"
            capture_cmd = f"{INFER_PATH} capture -- {build_cmd}"
            print(f"[PROGRESS]: capture project by {capture_cmd}")
            completed = utils.execute(capture_cmd, dir=self.project_root_dir)

            self.time_to_capture_original = time.time() - start_time

        return completed

    def preanal(self, debug):
        start_time = time.time()
        options = " ".join(
            [f"--test-methods {mthd}" for mthd in self.test_methods])

        if debug:
            analyze_cmd = f"{INFER_PATH} sprint --pfl --preanal --debug-level-analysis 1 {options}"
        else:
            analyze_cmd = f"{INFER_PATH} sprint --pfl --preanal {options}"

        print(analyze_cmd)
        ret = subprocess.run(analyze_cmd, shell=True,
                             cwd=self.project_root_dir)

        if ret.returncode == 12 or ret.returncode == 14:
            print(f"{FAIL} pre-analyze")
            exit(ret.returncode)

        if ret.returncode == 13:
            print(f"{WARNING} pre-analyze")

        self.time_to_analyze = time.time() - start_time

    def analyze(self, debug, pfl, pool, exnchecker, no_test, flonly=False):
        start_time = time.time()
        print(f"debug : {debug}")
        if int(debug) == 1:
            debug_opt = "-g --debug-level-analysis 3"
        elif int(debug) == 2:
            debug_opt = "-g --debug-level-analysis 4"
        elif debug:
            debug_opt = "-g"
        else:
            debug_opt = ""

        if flonly:
            options = f"{debug_opt} --localize-only"
        else:
            options = debug_opt

        options = options + " " + " ".join(
            [f"--test-methods {mthd}" for mthd in self.test_methods])

        if no_test:
            options = f" --no-test {options}"

        # options = " --scheduler restart " + options
        options = " --scheduler callgraph " + options
        options = f" --cpu-pool {pool} " + options

        if pool == -1:
            jobs = multiprocessing.cpu_count() // 2
        else:
            jobs = multiprocessing.cpu_count() // 8

        options = f"-j {jobs} {options}"

        if pfl:
            options = f"--pfl --bt-only {options}"
        else:
            options = f"--bt-only {options}"

        options = f"{'--exnchecker' if exnchecker else ''} {options}"

        analyze_cmd = f"{INFER_PATH} sprint  {options}"
        print(analyze_cmd)
        ret = subprocess.run(analyze_cmd, shell=True,
                             cwd=self.project_root_dir, stderr=subprocess.PIPE)
        stderr = ret.stderr.decode("utf-8") if ret.stderr else ""

        if ret.returncode == 0:
            recursive_cmd = f"{INFER_PATH} {debug_opt} sprint --recursive {options}"
            print(recursive_cmd)
            ret = subprocess.run(recursive_cmd, shell=True,
                                 cwd=self.project_root_dir)

        if ret.returncode != 0 and "InvalidDynamicInfo" in stderr:
            has_safe_results = os.path.exists(f"{self.project_root_dir}/feasible_abs_patches")
            if not has_safe_results:
                print(f"{ERROR}: no feasible patches found")
                exit(ret.returncode)
            elif "call" in stderr:
                print(f"{WARNING}: main analysis (mismatched call). Use pre-pruning results instead.")
                exit(13)
            elif "prune" in stderr:
                print(f"{WARNING}: main analysis (mismatched prune). Use pre-pruning results instead.")
                exit(14)

        if ret.returncode != 0 and "InvalidDynamicInfo" in stderr and "call" in stderr:
            print(f"{FAIL} main analysis (mismatched call)")
            exit(ret.returncode)

        if ret.returncode == 12:
            print(f"{FAIL} pre-analysis")
            exit(ret.returncode)

        if ret.returncode != 0:
            print(f"{FAIL} to analyze")
            exit(ret.returncode)
        self.time_to_analyze = time.time() - start_time

    def read_validation_results(self):
        if not os.path.isfile(
            results_file := f"{self.project_root_dir}/{self.VALIDATION_RESULTS_NAME}"
        ):
            return

        with open(results_file) as f:
            for row in f.readlines()[1:]:
                row = row.strip()
                fault_id = row.split(",")[0]
                results = row.split(",")[1:]
                print(f"{fault_id}, {results.count('X') == 0}")

    def logging(self, args):
        filename, line = args.path, args.line
        path = [path for path in glob.glob(
            f"**/{filename}", recursive=True)][0]
        print(f"check stack trace at line {line} in {path}")
        subprocess.call(
            "sed -i '"
            + line
            + "i try { throw new Exception (); } catch (Exception exnSprint) { exnSprint.printStackTrace(); }' "
            + path,
            cwd=self.project_root_dir,
            shell=True,
        )
        os.environ["D4J_DEBUG"] = "True"
        ret = self.d4j_test()

        with open(f"{self.project_root_dir}/{args.output}", "w") as f:
            f.write(ret.stdout)
            f.write(ret.stderr)
        # subprocess.call(test_cmd, cwd=self.project_root_dir, shell=True)
        print("checkout original file")
        subprocess.call(
            f"git checkout -- {path}", cwd=self.project_root_dir, shell=True
        )

        print("defects4j compile")
        self.d4j_build()

    def get_correct_lines(self):
        # class:line
        f = open(f"{INFER_HOME}/infer/resources/BugPositions.txt", "r")
        bug_position_lines = [
            l for l in f.readlines() if l.split("@")[0] == self.id]

        bug_locations = []
        for line in bug_position_lines:
            buggy_source_path = os.path.basename(line.split("@")[1])
            buggy_lines = gzoltar.parse_buggy_lines(line)
            for buggy_line in buggy_lines:
                bug_locations.append(f"{buggy_source_path}:{buggy_line}")
        return bug_locations

    def get_correct_lines2(self):
        # filepath:line
        f = open(f"{INFER_HOME}/infer/resources/BugPositions.txt", "r")
        bug_position_lines = [
            l for l in f.readlines() if l.split("@")[0] == self.id]

        bug_locations = []
        for line in bug_position_lines:
            buggy_source_path = line.split("@")[1]
            buggy_lines = gzoltar.parse_buggy_lines(line)
            for buggy_line in buggy_lines:
                bug_locations.append(f"{buggy_source_path}:{buggy_line}")
        return bug_locations

    def enumerate_abs_patches(self):
        cmd = f"{INFER_PATH} sprint --pfl --synthesis --no-static-prune --no-validate"
        ret = utils.execute(cmd, dir=self.project_root_dir)
        print(f"{self.id}: {ret.return_code}")

    def enumerate(self, mode, timeout=600, pfl=False):
        utils.remove_file_if_exists(
            f"{self.project_root_dir}/infer-out/sqlite_write_socket"
        )
        options = " ".join(
            [f"--test-methods {mthd}" for mthd in self.test_methods])
        cmd = f"timeout {timeout}s {INFER_HOME}/infer/bin/infer sprint --synthesis"
        if mode == "baseline":
            cmd = f"{cmd} --baseline"
        elif mode == "line":
            cmd = f"{cmd} --line-level"
        else:
            cmd = f"{cmd} --static-prune"

        cmd = f"{cmd} {options}"

        if pfl:
            cmd = f"{cmd} --pfl"

        jsonpath = f"{self.project_root_dir}/patches.json"
        utils.remove_file_if_exists(jsonpath)
        start_time = time.time()
        ret = utils.execute(cmd, timeout=timeout, dir=self.project_root_dir)
        if ret.return_code != 0:
            print(f"{ERROR}({self.id}): to run {cmd}\n{ret.stderr}")
        elapsed_time = time.time() - start_time

        if os.path.isfile(jsonpath):
            try:
                patches = [
                    patch for patch in utils.read_json_from_file(jsonpath)]
                return f"{self.id}, {len(patches)}, {elapsed_time}"

            except:
                patches = []
                print(f"{ERROR}: fail to parse {self.id}!!!!!!!!!!!!!!!")
                return f"{self.id}, {len(patches)}, fail!!!!"
        else:
            return f"{self.id}, 0, 0.0"

    def synthesis(self, mode, timeout=1200, pfl=False):
        options = " ".join(
            [f"--test-methods {mthd}" for mthd in self.test_methods])
        cmd = f"timeout {timeout}s {INFER_HOME}/infer/bin/infer sprint --synthesis --static-prune --abspatches"
        if pfl:
            cmd = f"{cmd} --pfl"
        if mode == "baseline":
            cmd = f"{cmd} --baseline"
        elif mode == "line":
            cmd = f"{cmd} --line-level"
        cmd = f"{cmd} {options}"

        print(cmd)

        jsonpath = f"{self.project_root_dir}/convert_ir_patches.json"
        utils.remove_file_if_exists(jsonpath)
        ret = subprocess.run(
            cmd,
            timeout=timeout,
            shell=True,
            cwd=self.project_root_dir,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        if os.path.isfile(jsonpath):
            try:
                patches = [
                    patch
                    for patch in utils.read_json_from_file(jsonpath)
                    if patch["rewriting_succeed"]
                ]
                return f"{self.id}, {len(patches)}"
            except:
                print(f"{ERROR}: fail to parse {self.id}!!!!!!!!!!!!!!!")
                return f"{self.id}, -1, fail!!!!"
        else:
            return f"{self.id}, 0"

    def repair(
        self,
        skip_conversion=False,
        skip_validation=False,
        timeout=10800,
        num_cpu_pools=16,
    ):
        cmd = f"{INFER_HOME}/infer/bin/infer sprint --synthesis --static-prune --validate --cpu-pool {os.getpid() % num_cpu_pools}"
        print(f"Repairing {self.id}: {cmd}")
        ret = subprocess.run(
            cmd,
            shell=True,
            cwd=self.project_root_dir,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )

        print(f"Repairing {self.id} ... Done!: {self.brief_status()}")
        return ret

    def init_gzoltar(self):
        if os.path.exists(GZOLTAR_HOME) is False:
            utils.execute(
                f"wget {GZOLTAR_URL} -O {RESOURCES_DIR}/gzoltar.tar.gz", dir=RESOURCES_DIR)
            utils.execute(
                f"tar -xvf {RESOURCES_DIR}/gzoltar.tar.gz", dir=RESOURCES_DIR)
            utils.execute(f"rm {RESOURCES_DIR}/gzoltar.tar", dir=RESOURCES_DIR)

        if os.path.exists(GZOLTAR_CLI_JAR) is False or os.path.exists(GZOLTAR_AGENT_JAR) is False:
            utils.execute(f"mvn install -DskipTests", dir=GZOLTAR_HOME)

    def gzoltar(self, verbosity=False):
        self.init_gzoltar()
        env = os.environ.copy()
        env['TZ'] = 'America/Los_Angeles'
        bid = self.id.split("_")[-1]

        if os.path.exists(f"{self.project_root_dir}/ochiai.ranking.rsv"):
            ret = utils.execute(
                f"diff -q {self.project_root_dir}/ochiai.ranking.csv.dropped {self.project_root_dir}/ochiai.ranking.csv", dir=self.project_root_dir, verbosity=1)
            if ret.return_code != 0:
                return f"{SUCCESS} to localize {self.id}"

        relevant_tests_file = f"{D4J_HOME}/framework/projects/{self.project_name}/relevant_tests/{bid}"
        relevant_tests = utils.execute(
            f"cat {relevant_tests_file} | sed 's/$/#*/' | sed ':a;N;$!ba;s/\\n/:/g'", dir=self.project_root_dir).stdout
        ser_file = f"{self.project_root_dir}/gzoltar.ser"
        list_cmd = f"java -cp {self.sprint_classes_dir}:{self.class_path}:{GZOLTAR_CLI_JAR} com.gzoltar.cli.Main listTestMethods {self.sprint_classes_dir} --outputFile {self.project_root_dir}/unit_tests.txt --includes {relevant_tests}"
        if verbosity:
            print(list_cmd)
        utils.execute(list_cmd, dir=self.project_root_dir)
        gzoltar_cmd = f"java -javaagent:{GZOLTAR_AGENT_JAR}=destfile={ser_file},buildlocation={self.sprint_classes_dir},inclnolocationclasses=false,output=FILE -cp {self.sprint_classes_dir}:{self.class_path}:{GZOLTAR_CLI_JAR} com.gzoltar.cli.Main runTestMethods --testMethods {self.project_root_dir}/unit_tests.txt --collectCoverage"
        report_cmd = f"java -cp {self.sprint_classes_dir}:{self.class_path}:{GZOLTAR_CLI_JAR} com.gzoltar.cli.Main faultLocalizationReport --buildLocation {self.sprint_classes_dir} --granularity line --inclPublicMethods --inclStaticConstructors --inclDeprecatedMethods --dataFile {ser_file} --outputDirectory {self.project_root_dir} --family sfl --formula ochiai --metric entropy --formatter txt"
        if not os.path.exists(f"{self.project_root_dir}/unit_tests.txt") or os.path.getsize(f"{self.project_root_dir}/unit_tests.txt") == 0:
            return f"{FAIL} to list unittests {self.id}"

        if verbosity:
            print(gzoltar_cmd)
            print(report_cmd)

        utils.execute(gzoltar_cmd, dir=self.project_root_dir,
                      env=env, timeout=7200)
        utils.execute(report_cmd, dir=self.project_root_dir)
        utils.execute(f"mv sfl/txt/ochiai.ranking.csv .",
                      dir=self.project_root_dir)
        
        with open(f"{self.project_root_dir}/ochiai.ranking.csv", "r") as f:
            if len(f.readlines()) == 1:
                return f"{FAIL} to localize {self.id}"

        utils.execute(f"rm -r sfl", dir=self.project_root_dir)
        last_index = utils.execute(f"python3 {SCRIPT_DIR}/gzoltar.py {self.id} {RESOURCES_DIR}/BugPositions.txt ochiai.ranking.csv ochiai.txt",
                      dir=self.project_root_dir).return_code
        if last_index == -1:
            msg = f"{FAIL} to correctly localize {self.id}"
        else:
            msg = f"{SUCCESS} to localize {self.id}"

        if verbosity:
            print(msg)
        return msg


"""
Given a classpath string, detect if it refers to JUnit and if the version is less than 4.11.
Returns True if it is a JUnit version < 4.11, else False.
"""
def is_junit_below_4_11(classpath_entry):
    # Normalize path and extract the filename
    filename = os.path.basename(classpath_entry)
    
    # Match Junit version
    match = re.match(r'(?:.*?junit)[-_.]?(\d+)\.(\d+)(?:\.(\d+))?\.jar', filename, re.IGNORECASE)
    
    if match:
        major, minor = int(match.group(1)), int(match.group(2))
        if major == 4 and minor < 11:
            return True
    return False

