import os
import json
import csv
import shutil
from pathlib import Path
import matplotlib.pyplot as plt

sessions = ["gpt-4.1_0311"]

def is_correct_patch(label_info: Path) -> bool:
    with open(label_info, "r") as f:
        return "incorrect" not in f.read()

def check_correct_exists(ap_id: int, bug: str) -> bool:
    """Return True if a correct patch exists in any session's PFL folder."""
    for session in sessions:
        pfl_bug_dir = Path("patches") / session / "PFL" / bug
        if not pfl_bug_dir.exists():
            continue
        label_info = pfl_bug_dir / str(ap_id) / "label_output.txt"
        if label_info.exists() and is_correct_patch(label_info):
            return True
    return False


def compute_bug_positions(ap_data, max_budget, bug):
    """Return baseline/pruned position and correctness for a bug."""
    # Baseline
    num_base = 0
    base_pos = -1
    is_base = False
    for ap in ap_data:
        num_base += 1
        if ap["pfl"] and check_correct_exists(ap["ap_id"], bug):
            base_pos = num_base
            is_base = True
            break
        if num_base >= max_budget:
            break

    # Pruned
    num_pruned = 0
    pruned_pos = -1
    is_pruned = False
    for ap in ap_data:
        if not ap["remains_after_prunning"]:
            continue
        num_pruned += 1
        if ap["pfl"] and check_correct_exists(ap["ap_id"], bug):
            pruned_pos = num_pruned
            is_pruned = True
            break
        if num_pruned >= max_budget:
            break

    return {
        "base_pos": base_pos,
        "base_found": int(is_base),
        "pruned_pos": pruned_pos,
        "pruned_found": int(is_pruned),
        "base_requests": min(num_base, max_budget),
        "pruned_requests": min(num_pruned, max_budget),
    }


def main():
    NFL_dir = Path("rawdata/gpt-4.1_0311/NFL")
    budgets = [100]
    correct_counts_baseline = []
    correct_counts_pruned = []
    
    result_dir = Path("rq2")
    result_dir.mkdir(parents=True, exist_ok=True)

    # Load D4J 1.x bug list
    d4j1_list = Path("d4j1.lst")
    if d4j1_list.exists():
        with open(d4j1_list, "r") as f:
            d4j1_bugs = {line.strip() for line in f if line.strip()}
    else:
        print("⚠️ d4j1.lst not found. Treating all bugs as D4J 2.0.")
        d4j1_bugs = set()

    # === Collect per-bug position data ===
    all_bug_data = {}
    for bug_dir in sorted(NFL_dir.iterdir()):
        bug = bug_dir.name
        ap_path = bug_dir / "ap.json"
        if not ap_path.exists():
            continue
        with open(ap_path) as f:
            all_bug_data[bug] = json.load(f)

    for max_budget in budgets:
        results_baseline = []
        results_pruned = []
        base_requests = []
        pruned_requests = []
        bug_details = []

        for bug, ap_data in all_bug_data.items():
            stats = compute_bug_positions(ap_data, max_budget, bug)
            correct_any = any(
                check_correct_exists(ap["ap_id"], bug) for ap in ap_data if ap["pfl"]
            )
            base_requests.append(stats["base_requests"])
            pruned_requests.append(stats["pruned_requests"])
            results_baseline.append((bug, stats["base_found"]))
            results_pruned.append((bug, stats["pruned_found"]))
            bug_details.append({
                "bug": bug,
                "base_pos": stats["base_pos"],
                "base_found_in_budget": stats["base_found"],
                "pruned_pos": stats["pruned_pos"],
                "pruned_found_in_budget": stats["pruned_found"],
                "correct_exists": int(correct_any),
            })

        # === Stats by D4J version ===
        d4j1_base = sum(x[1] for x in results_baseline if x[0] in d4j1_bugs)
        d4j2_base = sum(x[1] for x in results_baseline if x[0] not in d4j1_bugs)
        d4j1_pruned = sum(x[1] for x in results_pruned if x[0] in d4j1_bugs)
        d4j2_pruned = sum(x[1] for x in results_pruned if x[0] not in d4j1_bugs)

        d4j1_total = sum(1 for x in results_baseline if x[0] in d4j1_bugs)
        d4j2_total = sum(1 for x in results_baseline if x[0] not in d4j1_bugs)

        total_bugs = len(results_baseline)
        baseline_correct = sum(x[1] for x in results_baseline)
        pruned_correct = sum(x[1] for x in results_pruned)

        baseline_rate = baseline_correct / total_bugs * 100
        pruned_rate = pruned_correct / total_bugs * 100
    
        # === Request statistics ===
        valid_base_requests = [r for r in base_requests if 0 < r < max_budget]
        valid_pruned_requests = [r for r in pruned_requests if 0 < r < max_budget]

        avg_base = sum(valid_base_requests) / len(valid_base_requests) if valid_base_requests else 0
        avg_pruned = sum(valid_pruned_requests) / len(valid_pruned_requests) if valid_pruned_requests else 0

        min_base = min(valid_base_requests) if valid_base_requests else 0
        max_base = max(valid_base_requests) if valid_base_requests else 0
        min_pruned = min(valid_pruned_requests) if valid_pruned_requests else 0
        max_pruned = max(valid_pruned_requests) if valid_pruned_requests else 0

        # === Stats by project ===
        project_stats = {}
        for (bug, base_val), (_, pruned_val) in zip(results_baseline, results_pruned):
            proj_name = bug.split("_")[0]
            if bug in d4j1_bugs:
                proj = f"{proj_name}1"
            else:
                proj = f"{proj_name}2"

            if proj not in project_stats:
                project_stats[proj] = {
                    "num_bugs": 0,
                    "baseline_correct": 0,
                    "pruned_correct": 0
                }
            project_stats[proj]["num_bugs"] += 1
            project_stats[proj]["baseline_correct"] += base_val
            project_stats[proj]["pruned_correct"] += pruned_val

        # === Write summary.csv ===
        summary_file = result_dir / "summary.csv"
        with open(summary_file, "w", newline="") as f:
            writer = csv.writer(f)
            writer.writerow([
                "budget",
                "total_bugs",
                "d4j1.2_total_bugs",
                "d4j2.0_total_bugs",
                "baseline_correct",
                "pruned_correct",
                "baseline_rate(%)",
                "pruned_rate(%)",
                "avg_requests_baseline",
                "min_requests_baseline",
                "max_requests_baseline",
                "avg_requests_pruned",
                "min_requests_pruned",
                "max_requests_pruned",
                "d4j1.2_correct(base)",
                "d4j1.2_correct(pruned)",
                "d4j2.0_correct(base)",
                "d4j2.0_correct(pruned)"
            ])
            writer.writerow([
                max_budget,
                total_bugs,
                d4j1_total,
                d4j2_total,
                baseline_correct,
                pruned_correct,
                f"{baseline_rate:.2f}",
                f"{pruned_rate:.2f}",
                f"{avg_base:.2f}",
                min_base,
                max_base,
                f"{avg_pruned:.2f}",
                min_pruned,
                max_pruned,
                d4j1_base,
                d4j1_pruned,
                d4j2_base,
                d4j2_pruned
            ])
            writer.writerow([])

            writer.writerow(["project", "num_bugs", "baseline_correct", "pruned_correct"])
            for proj, stats in sorted(project_stats.items()):
                writer.writerow([
                    proj,
                    stats["num_bugs"],
                    stats["baseline_correct"],
                    stats["pruned_correct"]
                ])
            writer.writerow([])
            writer.writerow(["TOTAL", total_bugs, baseline_correct, pruned_correct])

        # Accumulate counts for bar chart
        correct_counts_baseline.append(baseline_correct)
        correct_counts_pruned.append(pruned_correct)

        # === Write bug_details.csv ===
        detail_file = result_dir / "bug_details.csv"
        with open(detail_file, "w", newline="") as f:
            writer = csv.DictWriter(f, fieldnames=list(bug_details[0].keys()))
            writer.writeheader()
            writer.writerows(sorted(bug_details, key=lambda r: r["bug"]))

        print(f"✅ Saved summary: {summary_file}")
        print(f"   total_bugs={total_bugs}, baseline={baseline_correct}, pruned={pruned_correct}")
        print(f"   avg_requests_base={avg_base:.2f}, avg_requests_pruned={avg_pruned:.2f}")
        print(f"✅ Saved bug details: {detail_file}")

    # === Budget sweep curve (rq2_compute.py generates data, rq2_plot.py renders) ===
    # Run rq2_compute.py if curve_data.csv is missing, then plot
    curve_csv = result_dir / "curve_data.csv"
    import subprocess
    if not curve_csv.exists():
        print("ℹ️  curve_data.csv not found. Running rq2_compute.py...")
        subprocess.run(["python3", "rq2_compute.py"], check=True)
    subprocess.run(["python3", "rq2_plot.py"], check=False)

    # === Bar chart ===
    x = range(len(budgets))
    width = 0.35
    plt.figure(figsize=(8, 5))
    plt.bar([i - width/2 for i in x], correct_counts_baseline, width, label="Baseline")
    plt.bar([i + width/2 for i in x], correct_counts_pruned, width, label="Pruned")
    plt.xticks(x, budgets)
    plt.xlabel("Max Budget")
    plt.ylabel("# of Correct Patches")
    plt.title("Correct Patches vs Budget")
    plt.legend()
    plt.grid(axis="y", linestyle="--", alpha=0.7)
    fig_path = result_dir / "barplot.png"
    plt.savefig(fig_path, dpi=200)
    plt.close()
    print(f"📊 Saved Figure: {fig_path}")


if __name__ == "__main__":
    main()
