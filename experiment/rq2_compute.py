"""
rq2_compute.py: Reads ap.json files and saves budget sweep raw data to CSV.
  rq2/curve_data.csv    : budget, base_count, pruned_count
  rq2/bug_details.csv   : per-bug details (at budget=100)
  rq2/summary.csv       : aggregate statistics (at budget=100)

Run rq2_plot.py separately to regenerate plots from the saved CSVs.
"""
import json
import csv
from pathlib import Path

SESSIONS   = ["gpt-4.1_0311"]
NFL_DIR    = Path("rawdata/gpt-4.1_0311/NFL")
RESULT_DIR = Path("rq2")
BUDGET_EVAL = 100          # budget for summary/bug_details
BUDGET_MAX  = 1000         # max budget for curve sweep

RESULT_DIR.mkdir(parents=True, exist_ok=True)


def is_correct_patch(label_path: Path) -> bool:
    return "incorrect" not in label_path.read_text()


def check_correct_exists(ap_id: int, bug: str) -> bool:
    for session in SESSIONS:
        label = Path("patches") / session / "PFL" / bug / str(ap_id) / "label_output.txt"
        if label.exists() and is_correct_patch(label):
            return True
    return False


def compute_bug_positions(ap_data, max_budget, bug):
    num_base, base_pos, is_base = 0, -1, False
    for ap in ap_data:
        num_base += 1
        if ap["pfl"] and check_correct_exists(ap["ap_id"], bug):
            base_pos = num_base
            is_base = True
            break
        if num_base >= max_budget:
            break

    num_pruned, pruned_pos, is_pruned = 0, -1, False
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
        "base_pos":       base_pos,
        "base_found":     int(is_base),
        "pruned_pos":     pruned_pos,
        "pruned_found":   int(is_pruned),
        "base_requests":  min(num_base,   max_budget),
        "pruned_requests":min(num_pruned, max_budget),
    }


def main():
    d4j1_bugs = {l.strip() for l in open("d4j1.lst") if l.strip()}

    # Load all ap.json files
    all_bug_data = {}
    for bug_dir in sorted(NFL_DIR.iterdir()):
        ap_path = bug_dir / "ap.json"
        if ap_path.exists():
            all_bug_data[bug_dir.name] = json.load(open(ap_path))

    print(f"Loaded {len(all_bug_data)} bugs")

    # ── 1. Budget sweep (curve_data.csv) ──────────────────────────────
    curve_path = RESULT_DIR / "curve_data.csv"
    with open(curve_path, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["budget", "base_count", "pruned_count"])
        for b in range(1, BUDGET_MAX + 1):
            bc = pc = 0
            for bug, ap_data in all_bug_data.items():
                s = compute_bug_positions(ap_data, b, bug)
                bc += s["base_found"]
                pc += s["pruned_found"]
            writer.writerow([b, bc, pc])
            if b % 100 == 0:
                print(f"  budget={b}: base={bc}, pruned={pc}")
    print(f"✅ Saved curve data: {curve_path}")

    # ── 2. bug_details.csv & summary.csv (budget=BUDGET_EVAL) ─────────
    results_base, results_pruned = [], []
    base_reqs, pruned_reqs = [], []
    bug_details = []

    for bug, ap_data in all_bug_data.items():
        s = compute_bug_positions(ap_data, BUDGET_EVAL, bug)
        correct_any = any(
            check_correct_exists(ap["ap_id"], bug) for ap in ap_data if ap["pfl"]
        )
        results_base.append((bug, s["base_found"]))
        results_pruned.append((bug, s["pruned_found"]))
        base_reqs.append(s["base_requests"])
        pruned_reqs.append(s["pruned_requests"])
        bug_details.append({
            "bug":                  bug,
            "base_pos":             s["base_pos"],
            "base_found_in_budget": s["base_found"],
            "pruned_pos":           s["pruned_pos"],
            "pruned_found_in_budget": s["pruned_found"],
            "correct_exists":       int(correct_any),
            "d4j_version":          "1.2" if bug in d4j1_bugs else "2.0",
        })

    detail_path = RESULT_DIR / "bug_details.csv"
    with open(detail_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(bug_details[0].keys()))
        writer.writeheader()
        writer.writerows(sorted(bug_details, key=lambda r: r["bug"]))
    print(f"✅ Saved bug details: {detail_path}")

    total = len(results_base)
    base_correct   = sum(v for _, v in results_base)
    pruned_correct = sum(v for _, v in results_pruned)

    d4j1_base   = sum(v for b, v in results_base   if b in d4j1_bugs)
    d4j1_pruned = sum(v for b, v in results_pruned if b in d4j1_bugs)
    d4j2_base   = sum(v for b, v in results_base   if b not in d4j1_bugs)
    d4j2_pruned = sum(v for b, v in results_pruned if b not in d4j1_bugs)

    valid_base   = [r for r in base_reqs   if 0 < r < BUDGET_EVAL]
    valid_pruned = [r for r in pruned_reqs if 0 < r < BUDGET_EVAL]

    summary_path = RESULT_DIR / "summary.csv"
    with open(summary_path, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["metric", "value"])
        writer.writerow(["budget", BUDGET_EVAL])
        writer.writerow(["total_bugs", total])
        writer.writerow(["baseline_correct", base_correct])
        writer.writerow(["pruned_correct", pruned_correct])
        writer.writerow(["d4j1_baseline", d4j1_base])
        writer.writerow(["d4j1_pruned", d4j1_pruned])
        writer.writerow(["d4j2_baseline", d4j2_base])
        writer.writerow(["d4j2_pruned", d4j2_pruned])
        writer.writerow(["avg_requests_base",   round(sum(valid_base)   / len(valid_base),   2) if valid_base   else 0])
        writer.writerow(["avg_requests_pruned", round(sum(valid_pruned) / len(valid_pruned), 2) if valid_pruned else 0])
    print(f"✅ Saved summary: {summary_path}")
    print(f"   total={total}, baseline={base_correct}, pruned={pruned_correct}")
    print(f"   D4J1.2: base={d4j1_base}, pruned={d4j1_pruned}")
    print(f"   D4J2.0: base={d4j2_base}, pruned={d4j2_pruned}")


if __name__ == "__main__":
    main()
