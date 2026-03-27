import os
import json
import csv
from pathlib import Path
import matplotlib.pyplot as plt
import pandas as pd

# ==== Constants ====
AVG_COMPILE_TIME = 3.724
AVG_VERIFY_TIME = 39.603  # sec (compile + test avg from validator_db)
SESSION = "gpt-4.1_0311"

# ==== Paths ====
RAW_DIR = Path("rawdata") / SESSION / "NFL"
ANALYSIS_TIME_PATH = Path("time.csv")  # bugid,Pre,Exn,Main,total
OUT_DIR = Path("rq3")
OUT_DIR.mkdir(parents=True, exist_ok=True)

# ==== Load static analysis time ====
analysis_time = {}
with open(ANALYSIS_TIME_PATH, newline="") as f:
    reader = csv.DictReader(f)
    for row in reader:
        bugid = row["bugid"].strip()
        analysis_time[bugid] = float(row["total"])

# ==== Collect results ====
summary_rows = []

for bug_dir in RAW_DIR.iterdir():
    bug = bug_dir.name
    ap_path = bug_dir / "ap.json"
    pfl_bug_dir = Path("patches") / SESSION / "PFL" / bug

    if not ap_path.exists():
        continue

    with open(ap_path, "r") as f:
        ap_data = json.load(f)

    # baseline
    num_req_base = len(ap_data)
    # pruned
    num_req_pruned = sum(1 for ap in ap_data if ap.get("remains_after_prunning", True))

    # Total time based on average verification time
    baseline_time = num_req_base * AVG_VERIFY_TIME
    ours_time = analysis_time.get(bug, 0.0) + num_req_pruned * AVG_VERIFY_TIME

    # Skip bugs where all patches are pruned
    if num_req_pruned == 0:
        continue
    
    print(bug, analysis_time.get(bug, 0.0))
    summary_rows.append({
        "bugid": bug,
        "baseline_requests": num_req_base,
        "pruned_requests": num_req_pruned,
        "analysis_time": analysis_time.get(bug, 0.0),
        "baseline_time": baseline_time,
        "ours_time": ours_time,
        "reduction_ratio": (1 - ours_time / baseline_time) * 100 if baseline_time > 0 else 0
    })

# ==== Save CSV ====
csv_path = OUT_DIR / "rq3_summary.csv"
with open(csv_path, "w", newline="") as f:
    fieldnames = [
        "bugid",
        "baseline_requests",
        "pruned_requests",
        "analysis_time",
        "baseline_time",
        "ours_time",
        "reduction_ratio",
    ]
    writer = csv.DictWriter(f, fieldnames=fieldnames)
    writer.writeheader()
    writer.writerows(summary_rows)

print(f"✅ Summary saved to {csv_path}")
print(f"Total bugs included: {len(summary_rows)}")

# ==== Boxplot (horizontal) ====
df = pd.DataFrame(summary_rows)

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

plot_path = OUT_DIR / "boxplot.png"
plt.savefig(plot_path, dpi=400, bbox_inches="tight")
plt.close()

print(f"✅ Boxplot saved to {plot_path}")

# ==== Histogram ====
plot_path = OUT_DIR / "histogram.png"

# Include all bugs (including negative reduction) for mean
ratios_all = df["reduction_ratio"]
mean_all = ratios_all.mean()

# Filter positive reductions for visualization
ratios_pos = ratios_all[ratios_all > 0]

plt.figure(figsize=(6, 3.8))

counts, bins, patches = plt.hist(
    ratios_pos,
    bins=20,
    range=(0, 100),        # fix x-axis range
    color="#6FA8DC",
    edgecolor="black",
    alpha=0.85,
    rwidth=1.0
)

# Mean line (including negative reductions)
plt.axvline(
    mean_all,
    color="red",
    linestyle="--",
    linewidth=1.5,
    label=f"Mean (all bugs) = {mean_all:.1f}%"
)

# Count labels above each bar
for count, bin_left, bin_right in zip(counts, bins[:-1], bins[1:]):
    if count > 0:
        plt.text(
            (bin_left + bin_right) / 2,
            count + 0.3,
            f"{int(count)}",
            ha="center",
            va="bottom",
            fontsize=8,
            color="black"
        )

plt.xlabel("Estimated Repair Time Reduction Rate (%)")
plt.ylabel("# Bugs per Reduction Interval")
plt.xlim(0, 100)
plt.legend(loc="upper right", frameon=False)
plt.tight_layout()
plt.savefig(plot_path, dpi=400, bbox_inches="tight")
plt.close()

print(f"✅ Histogram saved to {plot_path}")
print(f"📊 Mean reduction ratio (all): {mean_all:.1f}%")
print(f"📈 Median reduction ratio (all): {ratios_all.median():.1f}%")

# ==== Additional statistics ====
avg_base = df["baseline_time"].mean()
avg_ours = df["ours_time"].mean()
avg_reduction = (1 - avg_ours / avg_base) * 100
print(f"\n📊 Average baseline time: {avg_base/3600:.2f} hr")
print(f"📊 Average ours time:     {avg_ours/3600:.2f} hr")
print(f"📉 Average reduction:     {avg_reduction:.1f}%")
