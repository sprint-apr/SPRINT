import sys
import re
import typer

app = typer.Typer()
OCHIAI_RANKING_CSV_NAME = "ochiai.txt"

def remove_parentheses(s):
    return re.sub(r'\(.*?\)', '', s)

def find_last_idx(ochiai_lines, buggy_source_path, buggy_lines):
    buggy_class_path = buggy_source_path.replace("/", ".")

    # Find the minimum score that covers all the buggy lines
    min_score = 1.0
    for idx, line in enumerate(ochiai_lines):
        if line == "name;suspiciousness_value":
            continue

        line_no = int(line.split(":")[1].split(";")[0])
        score = float(line.split(":")[1].split(";")[1])

        if line_no not in buggy_lines:
            continue

        cls = ".".join(line.split("#")[0].split("$")[0:2])
        if cls not in buggy_class_path:
            continue

        min_score = score
        buggy_lines.remove(line_no)
        if buggy_lines == []:
            break

    # Find the last index of min scored line
    last_index = -1
    for idx, line in enumerate(ochiai_lines):
        if line == "name;suspiciousness_value":
            continue

        score = float(line.split(":")[1].split(";")[1])
        if score < min_score:
            break

        last_index = idx

    return last_index


def parse_buggy_lines(line):
    line_numbers = []
    for chunk in line.strip().split("@")[2].split(","):
        # For Closure-49 case
        if chunk == "":
            continue

        if chunk.isnumeric():
            line_numbers.append(int(chunk))
            continue

        [begin, end] = chunk.split("-")
        line_numbers.extend(range(int(begin), int(end) + 1))

    return line_numbers


def revise_line(lines):
    results = []
    for line in lines:
        if "name;suspiciousness_value" in line:
            continue
        line = remove_parentheses(line)
        line = line.replace(';', ',')
        [cp, line_score] = line.split(':')
        [cp, _] = cp.split("#")
        [cp, cls] = cp.split("$")[0:2]
        results.append(f"{cp}.{cls}#{line_score}")
    return results 
        

@app.command()
def drop_ranks_under_buggy_position(bug_id, bug_positions, ranking_csv, output_csv):
    with open(bug_positions, "r") as f:
        # Bug positions can be multiple for a single bug.
        bug_position_lines = [l for l in f.readlines() if l.split("@")[0] == bug_id]

        bug_locations = []
        for line in bug_position_lines:
            buggy_source_path = line.split("@")[1]
            buggy_lines = parse_buggy_lines(line)
            bug_locations.append((buggy_source_path, buggy_lines))

    last_index = -1
    with open(ranking_csv, "r") as f:
        ochiai_lines = [l.strip() for l in f.readlines()]
        for buggy_source_path, buggy_lines in bug_locations:
            last_index = max(
                last_index, find_last_idx(ochiai_lines, buggy_source_path, buggy_lines)
            )

    if last_index == -1:
        print(f"Could not find any matched lines for {bug_id}")
        last_index = len(ochiai_lines) - 1

    ochiai_lines = revise_line(ochiai_lines)
    with open(output_csv, "w") as f:
        for line in ochiai_lines[:last_index]:
            f.write(line + "\n")

    return last_index


if __name__ == "__main__":
    app()
