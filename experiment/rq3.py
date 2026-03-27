import json
import csv
from pathlib import Path
import matplotlib.pyplot as plt
import pandas as pd

AVG_VERIFY_TIME = 39.603  # sec (compile + test avg from validator_db)
SESSION = "gpt-4.1_0311"

RAW_DIR = Path("rawdata") / SESSION / "NFL"
ANALYSIS_TIME_PATH = Path("time.csv")
OUT_DIR = Path("rq3")
OUT_DIR.mkdir(parents=True, exist_ok=True)

analysis_time = {}
with open(ANALYSIS_TIME_PATH, newline="") as f:
    for row in csv.DictReader(f):
        analysis_time[row["bugid"].strip()] = float(row["total"])


def collect_rows(line_level_only: bool) -> list:
    rows = []
    for bug_dir in RAW_DIR.iterdir():
        bug = bug_dir.name
        ap_path = bug_dir / "ap.json"
        if not ap_path.exists():
            continue

        ap_data = json.load(open(ap_path))
        if line_level_only:
            ap_data = [ap for ap in ap_data if ap.get("is_line_level", False)]

        num_req_base   = len(ap_data)
        num_req_pruned = sum(1 for ap in ap_data if ap.get("remains_after_prunning", True))

        if num_req_base == 0 or num_req_pruned == 0:
            continue

        at = analysis_time.get(bug, 0.0)
        baseline_time = num_req_base * AVG_VERIFY_TIME
        ours_time     = at + num_req_pruned * AVG_VERIFY_TIME

        rows.append({
            "bugid":              bug,
            "baseline_requests":  num_req_base,
            "pruned_requests":    num_req_pruned,
            "analysis_time":      at,
            "baseline_time":      baseline_time,
            "ours_time":          ours_time,
            "reduction_ratio":    (1 - ours_time / baseline_time) * 100 if baseline_time > 0 else 0,
        })
    return rows


def plot_histogram(df: pd.DataFrame, out_path: Path):
    ratios_all = df["reduction_ratio"]
    mean_all   = ratios_all.mean()
    ratios_pos = ratios_all[ratios_all > 0]

    plt.figure(figsize=(6, 3.8))
    counts, bins, _ = plt.hist(
        ratios_pos,
        bins=20,
        range=(0, 100),
        color="#6FA8DC",
        edgecolor="black",
        alpha=0.85,
        rwidth=1.0,
    )
    plt.axvline(mean_all, color="red", linestyle="--", linewidth=1.5,
                label=f"Mean (all bugs) = {mean_all:.1f}%")
    for count, bl, br in zip(counts, bins[:-1], bins[1:]):
        if count > 0:
            plt.text((bl + br) / 2, count + 0.3, f"{int(count)}",
                     ha="center", va="bottom", fontsize=8)
    plt.xlabel("Estimated Repair Time Reduction Rate (%)")
    plt.ylabel("# Bugs per Reduction Interval")
    plt.xlim(0, 100)
    plt.legend(loc="upper right", frameon=False)
    plt.tight_layout()
    plt.savefig(out_path, dpi=400, bbox_inches="tight")
    plt.close()
    print(f"✅ Histogram saved to {out_path}")
    print(f"   Mean={mean_all:.1f}%, Median={ratios_all.median():.1f}%")


def plot_boxplot(df: pd.DataFrame, out_path: Path):
    plt.figure(figsize=(8, 3))
    plt.boxplot(
        [df["baseline_time"], df["ours_time"]],
        tick_labels=["w/o pruning", "w/ pruning"],
        vert=False,
        patch_artist=True,
        widths=0.4,
        showmeans=False,
        showfliers=False,
        medianprops=dict(color="black", linewidth=1.3),
        boxprops=dict(facecolor="#C9DAF8", edgecolor="black", linewidth=1.0),
        whiskerprops=dict(color="black", linewidth=1.0),
        capprops=dict(color="black", linewidth=1.0),
    )
    plt.xscale("log")
    plt.xlabel("End-to-end repair time (sec)")
    plt.tight_layout()
    plt.savefig(out_path, dpi=400, bbox_inches="tight")
    plt.close()
    print(f"✅ Boxplot saved to {out_path}")


for label, line_only in [("template", False), ("line", True)]:
    rows = collect_rows(line_level_only=line_only)
    df   = pd.DataFrame(rows)

    csv_path = OUT_DIR / f"rq3_summary_{label}.csv"
    df.to_csv(csv_path, index=False)
    print(f"✅ Summary saved to {csv_path} ({len(rows)} bugs)")

    plot_histogram(df, OUT_DIR / f"histogram_{label}.png")
    plot_boxplot(df,   OUT_DIR / f"boxplot_{label}.png")

    avg_base = df["baseline_time"].mean()
    avg_ours = df["ours_time"].mean()
    print(f"   Avg baseline: {avg_base/3600:.2f} hr, ours: {avg_ours/3600:.2f} hr, "
          f"reduction: {(1-avg_ours/avg_base)*100:.1f}%\n")
