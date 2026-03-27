import json
from pathlib import Path
import time
import os
import glob
import re
import signal
import csv
from subprocess import Popen, PIPE, TimeoutExpired
from multiprocessing import Pool
from time import monotonic as timer
from copy import deepcopy
from colorama import Fore, Style
from dacite import from_dict as _from_dict
from typing import List, Dict, Any
import xml.etree.ElementTree as ET
import requests

class Ret:
    def __init__(self, stdout, stderr, return_code, time):
        self.stdout = stdout.decode('iso-8859-1', errors='ignore')
        self.stderr = stderr.decode('iso-8859-1', errors='ignore')
        self.return_code = return_code
        self.time = time

ERROR = f"{Fore.RED}[ERROR]{Style.RESET_ALL}"
FAIL = f"{Fore.YELLOW}[FAIL]{Style.RESET_ALL}"
WARNING = f"{Fore.MAGENTA}[WARNING]{Style.RESET_ALL}"
SUCCESS = f"{Fore.CYAN}[SUCCESS]{Style.RESET_ALL}"
TIMEOUT = f"{Fore.LIGHTMAGENTA_EX}[TIMEOUT]{Style.RESET_ALL}"
PROGRESS = f"{Fore.LIGHTWHITE_EX}[PROGRESS]{Style.RESET_ALL}"
SERIOUS = f"{Fore.LIGHTRED_EX}[SERIOUS]{Style.RESET_ALL}"
ENV = os.environ

def make_dir_if_not_exists(path):
    if os.path.isdir(path) is False:
        os.mkdir(path)


def execute(cmd, dir=None, env=None, timeout=1200, verbosity=0):
    if verbosity >= 1:
        print(f"EXECUTE {cmd} AT {os.path.basename(dir)}")

    start = timer()
    try:
        process = Popen(
            cmd,
            shell=True,
            stdout=PIPE,
            stderr=PIPE,
            cwd=dir,
            env=env,
            preexec_fn=os.setsid,
        )
        stdout, stderr = process.communicate(timeout=timeout)
        returncode = process.returncode
    except TimeoutExpired:
        # send signal to the process group
        os.killpg(process.pid, signal.SIGINT)
        print(f"{TIMEOUT} occurs during executing {cmd[:20]} at {dir}")
        stdout, stderr = b"", b""
        returncode = 124
    except OSError:
        print(f"{ERROR}: failed to execute {cmd} at {dir} (maybe it is too long...)")
        stdout, stderr = b"", b""
        returncode = -1

    ret = Ret(stdout, stderr, returncode, timer() - start)

    if ret.return_code != 0:
        if verbosity >= 1:
            print(f"{ERROR} - FAILED TO EXECUTE {cmd} AT {os.path.basename(dir)}")
    return ret

def upload_csv_to_google_sheet(
        csv_path: Path,
        script_url: str,
        sheet_id: str,
        tab_name: str):
    full_url = f"{script_url}?sheet_id={sheet_id}&tab_name={tab_name}"
    csv_data = csv_path.read_bytes()

    response = requests.post(
        full_url,
        headers={'Content-Type': 'text/plain'},
        data=csv_data
    )

    if response.status_code == 200:
        print(f"✅ CSV uploaded to tab '{tab_name}' successfully.")
    else:
        print(f"❌ Failed to upload: {response.status_code}")
        print(response.text)

