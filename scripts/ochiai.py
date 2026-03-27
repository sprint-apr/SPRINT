import os
from config import *
import re


def filepath(bug_id):
    return f"{RESOURCES_DIR}/ochiai/{bug_id}/ochiai.txt"


def parse(bug_id):
    results = []
    if not os.path.isfile(filepath(bug_id)):
        print(f"{WARNING}: no ochiai for {bug_id}")
        return results

    with open(filepath(bug_id), 'r') as f:
        # org.apache.commons.lang3.time.FastDateParser#180,0.7071067811865475
        for line in f.readlines():
            if line == "":
                continue
            line = line.replace("\n", "")
            [cp_line, score] = line.split(",")[:2]
            [cp, line] = cp_line.split("#")
            results.append((cp, int(line), float(score)))
    return results


# get FL data from tare
def tare_filepath(bug_id):
    [repo, id] = bug_id.split('_')
    if bug_id in D4J_1:
        return f"{RESOURCES_DIR}/location/ochiai/{repo.lower()}/{id}.txt"
    else:
        return f"{RESOURCES_DIR}/location2/{repo}/{id}/parsed_ochiai_result"


def tare_parse(bug_id):
    results = []
    with open(tare_filepath(bug_id), 'r') as f:
        if bug_id in D4J_1:
            # org.apache.commons.lang3.time.FastDateParser#180,0.7071067811865475,(1,1)
            for line in f.readlines():
                if line == "":
                    continue
                line = line.replace("\n", "")
                [cp_line, score] = line.split(",")[:2]
                [cp, line] = cp_line.split("#")
                results.append((cp, line, score))
        else:
            # org.apache.commons.cli.OptionBuilder#301	0.2886751345948129
            for line in f.readlines():
                if line == "":
                    continue
                line = line.replace("\n", "")
                [cp_line, score] = re.split(r'[ \t]+', line)
                [cp, line] = re.split(r'#|:', cp_line)
                results.append((cp, line, score))
    return results


def tare_parse_and_store_to(base_dir, bug_id):
    if os.path.isfile(tare_filepath(bug_id)) is False:
        print(f"{WARNING}: no ochiai for {bug_id}")
        return

    parsed_results = tare_parse(bug_id)
    os.makedirs(f"{base_dir}/{bug_id}", exist_ok=True)
    with open(f"{base_dir}/{bug_id}/ochiai.txt", 'w') as f:
        for (cp, line, score) in parsed_results:
            f.write(f"{cp}#{line},{score}\n")

    if bug_id in D4J_1:
        with open(f"{base_dir}/d4j1_with_ochiai.lst", 'a') as f:
            f.write(f"{bug_id}\n")
    else:
        with open(f"{base_dir}/d4j2_with_ochiai.lst", 'a') as f:
            f.write(f"{bug_id}\n")
