import os
import socket
from pathlib import Path
from colorama import Fore, Style

# PATH VARIABLES
PROJECT_ROOT = Path(__file__).absolute().parent.parent
SCRIPT_DIR = Path(__file__).absolute().parent
D4J_HOME = os.environ["D4J_HOME"]
RESOURCES_DIR = f"{PROJECT_ROOT}/tool/resources"

INFER_HOME = f"{PROJECT_ROOT}/tool/sabfl"
INFER_PATH = f"{INFER_HOME}/infer/bin/infer"
DEFECTS4J = f"{D4J_HOME}/framework/bin/defects4j"

AGENT_JAR_PATH = (
    PROJECT_ROOT / "tool/components/tracer/target/sprint.tracer-1.0-SNAPSHOT-all.jar"
)
assert os.path.isfile(AGENT_JAR_PATH)

# VALIDATOR VARIABLES
D4J_CLASSPATH_FILE_NAME = ".classpath.d4j"
JUNIT_CLASSPATH = (
    f"{PROJECT_ROOT}/tool/components/verifier/target/sprint.verifier-1.0.0.jar"
)
JUNIT_CORE_CLASS = "sprint.verifier.junit.JUnitRunner"
SYNTHESIS_RESULT_JSON_NAME = "convert_ir_patches.json"
VALIDATION_DB_PATH = f"{PROJECT_ROOT}/scripts/validation.db"

ERROR = f"{Fore.RED}[ERROR]{Style.RESET_ALL}"
FAIL = f"{Fore.YELLOW}[FAIL]{Style.RESET_ALL}"
WARNING = f"{Fore.MAGENTA}[WARNING]{Style.RESET_ALL}"
SUCCESS = f"{Fore.CYAN}[SUCCESS]{Style.RESET_ALL}"
TIMEOUT = f"{Fore.LIGHTMAGENTA_EX}[TIMEOUT]{Style.RESET_ALL}"
PROGRESS = f"{Fore.LIGHTWHITE_EX}[PROGRESS]{Style.RESET_ALL}"
SERIOUS = f"{Fore.LIGHTRED_EX}[SERIOUS]{Style.RESET_ALL}"

# DEFECTS4J VARIABLES
D4J_CLASSPATH_FILE_NAME = ".classpath.d4j"
D4J_ALL_TESTS_FILE_NAME = "defects4j.tests.all"
D4J_1 = [bug_id.replace("\n", "") for bug_id in open(
    f'{RESOURCES_DIR}/d4j1_with_ochiai.lst', 'r').readlines()]

D4J_2 = [bug_id.replace("\n", "") for bug_id in open(
    f'{RESOURCES_DIR}/d4j2_with_ochiai.lst', 'r').readlines()]

BENCHMARKS_LIST = D4J_1 + D4J_2

# JDK VARIABLES
JDK_8 = "/usr/lib/jvm/java-8-openjdk-amd64"

MSG_TEST_FAIL = "test failures"
MSG_ASSERT_FAIL = "Assertion"
MSG_COMPILE_FAIL = "Compilation failure"
MSG_NPE = "NullPointerException"

HOST_NAME = socket.gethostname()
GZOLTAR_HOME = f"{RESOURCES_DIR}/gzoltar-1.7.2"
GZOLTAR_URL = "https://github.com/GZoltar/gzoltar/archive/refs/tags/v1.7.2.tar.gz"
GZOLTAR_CLI_JAR = f"{GZOLTAR_HOME}/com.gzoltar.cli/target/com.gzoltar.cli-1.7.2-jar-with-dependencies.jar"
GZOLTAR_AGENT_JAR = f"{GZOLTAR_HOME}/com.gzoltar.agent.rt/target/com.gzoltar.agent.rt-1.7.2-all.jar"
