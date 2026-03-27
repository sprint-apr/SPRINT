"""
rq2_plot.py: rq2_compute.py가 생성한 CSV를 읽어 그래프만 그림.
  Input:  rq2/curve_data.csv, rq2/summary.csv
  Output: rq2/curve_budget.png, rq2/compare_budget100.png
"""
import csv
from pathlib import Path
import matplotlib.pyplot as plt

RESULT_DIR = Path("rq2")

PRIOR_TOOLS = [
    ("CoCoNuT",       33),
    ("SimFix",        34),
    ("CURE",          36),
    ("TransplantFix", 42),
    ("SelfAPR",       45),
    ("DEAR",          47),
    ("TBar",          49),
    ("RewardRepair",  53),
    ("AlphaRepair",   64),
    ("Recoder",       70),
    ("ITER",          74),
    ("tenure",        84),
]


def load_curve():
    path = RESULT_DIR / "curve_data.csv"
    budgets, base, pruned, base_line, pruned_line = [], [], [], [], []
    with open(path) as f:
        for row in csv.DictReader(f):
            budgets.append(int(row["budget"]))
            base.append(int(row["base_count"]))
            pruned.append(int(row["pruned_count"]))
            base_line.append(int(row.get("base_line_count", 0)))
            pruned_line.append(int(row.get("pruned_line_count", 0)))
    return budgets, base, pruned, base_line, pruned_line


def load_summary():
    path = RESULT_DIR / "summary.csv"
    d = {}
    with open(path) as f:
        for row in csv.reader(f):
            if len(row) == 2:
                d[row[0]] = row[1]
    return d


BUDGET_DISPLAY = 500  # x-axis cap for plot


def _plot_single_curve(ax, budgets, base, pruned, ylim=140):
    mask = [b <= BUDGET_DISPLAY for b in budgets]
    b = [budgets[i] for i in range(len(budgets)) if mask[i]]
    ba = [base[i]   for i in range(len(base))    if mask[i]]
    pr = [pruned[i] for i in range(len(pruned))  if mask[i]]
    ax.plot(b, pr, color="blue", linestyle="--", linewidth=2, label="w/ pruning")
    ax.plot(b, ba, color="red",  linestyle="-",  linewidth=2, label="w/o pruning")
    ax.set_xlim(1, BUDGET_DISPLAY)
    ax.set_ylim(0, ylim)
    ax.set_xticks(range(0, BUDGET_DISPLAY + 1, 100))
    ax.set_xlabel("Maximum # of LLM Queries per Bug (Budget)", fontsize=13)
    ax.set_ylabel("# of Bugs with Correct Patch Found", fontsize=13)
    ax.tick_params(axis="both", labelsize=12)
    ax.legend(loc="lower right", fontsize=12)
    ax.grid(axis="both", linestyle="--", alpha=0.5)


def plot_curve(budgets, base, pruned, base_line, pruned_line):
    # Template-level
    fig, ax = plt.subplots(figsize=(8, 6))
    _plot_single_curve(ax, budgets, base, pruned, ylim=140)
    plt.tight_layout()
    out = RESULT_DIR / "curve_budget_template.png"
    plt.savefig(out, dpi=200, bbox_inches="tight")
    plt.close()
    print(f"✅ Saved: {out}")

    # Line-level
    fig, ax = plt.subplots(figsize=(8, 6))
    _plot_single_curve(ax, budgets, base_line, pruned_line, ylim=120)
    plt.tight_layout()
    out = RESULT_DIR / "curve_budget_line.png"
    plt.savefig(out, dpi=200, bbox_inches="tight")
    plt.close()
    print(f"✅ Saved: {out}")


def plot_compare(base_at100, pruned_at100):
    tools  = [t for t, _ in PRIOR_TOOLS] + ["SPRINT\n(w/o pruning)", "SPRINT\n(w/ pruning)"]
    values = [v for _, v in PRIOR_TOOLS]  + [base_at100, pruned_at100]
    colors = ["#AAAAAA"] * len(PRIOR_TOOLS) + ["#E74C3C", "#2980B9"]

    fig, ax = plt.subplots(figsize=(10, 5))
    bars = ax.bar(tools, values, color=colors, edgecolor="black", linewidth=0.6)
    for bar, val in zip(bars, values):
        ax.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.8,
                str(val), ha="center", va="bottom", fontsize=9)
    ax.set_ylabel("# of Bugs with Correct Patch Found")
    ax.set_xlabel("Tool")
    ax.tick_params(axis="x", labelsize=8)
    ax.grid(axis="y", linestyle="--", alpha=0.5)
    plt.tight_layout()
    out = RESULT_DIR / "compare_budget100.png"
    plt.savefig(out, dpi=200, bbox_inches="tight")
    plt.close()
    print(f"✅ Saved: {out}")


def main():
    budgets, base, pruned, base_line, pruned_line = load_curve()
    summary = load_summary()

    plot_curve(budgets, base, pruned, base_line, pruned_line)

    base_at100   = int(summary.get("baseline_correct", base[99]))
    pruned_at100 = int(summary.get("pruned_correct",   pruned[99]))
    plot_compare(base_at100, pruned_at100)

    print(f"\nbudget=100: baseline={base_at100}, pruned={pruned_at100}")


if __name__ == "__main__":
    main()
