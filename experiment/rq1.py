import json
from pathlib import Path
import csv

sessions = ["gpt-4.1-nano_0310", "gpt-4.1_0311"]

BUDGET = 500  # max AP queries per bug (None = unlimited)

input_tokens = {
    "gpt-4.1-nano_0310": 1015.43,
    "gpt-4.1_0311":      1017.11,
    "gpt-4.1_0312":      1020.26,
}
output_tokens = {
    "gpt-4.1-nano_0310": 186.79,
    "gpt-4.1_0311":      203.06,
    "gpt-4.1_0312":      204.49,
}


def is_correct(label_file: Path) -> bool:
    content = label_file.read_text().strip()
    return content == "correct"


def load_labels() -> dict:
    """label_output.txt == 'correct' 인 버그 {bug_id: True} 로드."""
    labels = {}
    for session in sessions:
        pfl_dir = Path("patches") / session / "PFL"
        if not pfl_dir.exists():
            continue
        for bug_dir in pfl_dir.iterdir():
            if not bug_dir.is_dir() or labels.get(bug_dir.name):
                continue
            for ap_dir in bug_dir.iterdir():
                if not ap_dir.is_dir():
                    continue
                label_file = ap_dir / "label_output.txt"
                if label_file.exists() and is_correct(label_file):
                    labels[bug_dir.name] = True
                    break
    return labels


labels = load_labels()


def has_correct_patch(ap_dir: Path) -> bool:
    """ap_dir 안에 correct label이 있으면 True."""
    label = ap_dir / "label_output.txt"
    return label.exists() and is_correct(label)


def compute_bug_stats(ap_list: list, pfl_bug_dir: Path, budget=None) -> dict:
    """Count requests and correctness up to budget APs (None = unlimited)."""
    num_base, is_patched_base = 0, False
    for ap in ap_list:
        num_base += 1
        if ap["pfl"] and pfl_bug_dir.exists():
            if has_correct_patch(pfl_bug_dir / str(ap["ap_id"])):
                is_patched_base = True
                break
        if budget and num_base >= budget:
            break

    num_pruned, is_patched_pruned = 0, False
    for ap in ap_list:
        if not ap.get("remains_after_prunning", True):
            continue
        num_pruned += 1
        if ap["pfl"] and pfl_bug_dir.exists():
            if has_correct_patch(pfl_bug_dir / str(ap["ap_id"])):
                is_patched_pruned = True
                break
        if budget and num_pruned >= budget:
            break

    return {
        "num_requests_base": num_base,
        "is_patched_base": is_patched_base,
        "num_requests_pruned": num_pruned,
        "is_patched_pruned": is_patched_pruned,
    }


def process_level(session: str, level: str, bug_results: list, summary_writer):
    """집계 및 summary row 작성. level: 'template' | 'line'"""
    results_baseline = [{"bug": b, "num_requests": s["num_requests_base"], "is_patched": s["is_patched_base"]} for b, s in bug_results]
    results_pruned   = [{"bug": b, "num_requests": s["num_requests_pruned"], "is_patched": s["is_patched_pruned"]} for b, s in bug_results]

    correct_lost = 0
    lost_bugs = []
    for base, pruned in zip(results_baseline, results_pruned):
        bug = base["bug"]
        if base["is_patched"] and not pruned["is_patched"]:
            correct_lost += 1
            lost_bugs.append(bug)

    total_correct_base   = sum(1 for d in results_baseline if d["is_patched"])
    total_correct_pruned = sum(1 for d in results_pruned   if d["is_patched"])
    correct_retention = round((total_correct_base - correct_lost) / total_correct_base * 100, 1) if total_correct_base else 0

    total_req_base   = sum(d["num_requests"] for d in results_baseline)
    total_req_pruned = sum(d["num_requests"] for d in results_pruned)

    base_input    = input_tokens[session]  * total_req_base
    base_output   = output_tokens[session] * total_req_base
    pruned_input  = input_tokens[session]  * total_req_pruned
    pruned_output = output_tokens[session] * total_req_pruned

    print(f"  [{level}] baseline: req={total_req_base}, correct={total_correct_base} | pruned: req={total_req_pruned}, correct={total_correct_pruned}")
    print(f"    correct lost={correct_lost}/{total_correct_base}, retention={correct_retention}%")
    if lost_bugs:
        print(f"    lost correct bugs: {lost_bugs}")

    summary_writer.writerow({
        "session": session,
        "level": level,
        "baseline_requests": total_req_base,
        "baseline_correct": total_correct_base,
        "baseline_input_tokens": base_input,
        "baseline_output_tokens": base_output,
        "pruned_requests": total_req_pruned,
        "pruned_correct": total_correct_pruned,
        "pruned_input_tokens": pruned_input,
        "pruned_output_tokens": pruned_output,
        "correct_lost": correct_lost,
        "correct_retention(%)": correct_retention,
    })


def process_session(session: str, summary_writer, detail_writer):
    print(f"\nProcessing session: {session}")
    NFL_dir = Path("rawdata") / session / "NFL"

    template_results = []  # (bug, stats)
    line_results     = []

    for bug_dir in sorted(NFL_dir.iterdir()):
        bug = bug_dir.name
        pfl_bug_dir = Path("patches") / session / "PFL" / bug
        ap_path = bug_dir / "ap.json"
        if not ap_path.exists():
            continue

        with open(ap_path) as f:
            ap_data = json.load(f)

        has_line_level_field = ap_data and "is_line_level" in ap_data[0]

        # template = 전체 AP, line = template의 서브셋 (is_line_level==True)
        line_aps = [ap for ap in ap_data if ap.get("is_line_level", False)]

        t_stats = compute_bug_stats(ap_data, pfl_bug_dir, budget=BUDGET)
        template_results.append((bug, t_stats))

        detail_writer.writerow({
            "bug": bug,
            "session": session,
            "level": "template",
            "total_aps": len(ap_data),
            "baseline_requests": t_stats["num_requests_base"],
            "baseline_correct": int(t_stats["is_patched_base"]),
            "pruned_requests": t_stats["num_requests_pruned"],
            "pruned_correct": int(t_stats["is_patched_pruned"]),
            "request_reduction": t_stats["num_requests_base"] - t_stats["num_requests_pruned"],
        })

        if has_line_level_field:
            l_stats = compute_bug_stats(line_aps, pfl_bug_dir, budget=BUDGET)
            line_results.append((bug, l_stats))
            detail_writer.writerow({
                "bug": bug,
                "session": session,
                "level": "line",
                "total_aps": len(line_aps),
                "baseline_requests": l_stats["num_requests_base"],
                "baseline_correct": int(l_stats["is_patched_base"]),
                "pruned_requests": l_stats["num_requests_pruned"],
                "pruned_correct": int(l_stats["is_patched_pruned"]),
                "request_reduction": l_stats["num_requests_base"] - l_stats["num_requests_pruned"],
            })

    result_dir = Path(f"rq1/{session}")
    result_dir.mkdir(parents=True, exist_ok=True)

    process_level(session, "template", template_results, summary_writer)
    if line_results:
        process_level(session, "line", line_results, summary_writer)


def render_table(rows) -> str:
    def M(v): return f"{float(v)/1e6:.1f}M"
    def pct(v): return f"{v}%"

    col_headers = [
        ("session", 22), ("level", 9),
        ("base_req", 9), ("base_correct", 12),
        ("base_tok(I+O)", 14),
        ("prune_req", 10), ("prune_correct", 13),
        ("prune_tok(I+O)", 15),
        ("corr_lost", 10), ("corr_ret", 9),
    ]
    fmt = "  ".join(f"{{:<{w}}}" for _, w in col_headers)
    lines = [fmt.format(*[h for h, _ in col_headers]), "-" * len(fmt.format(*[""] * len(col_headers)))]

    prev_session = None
    for r in rows:
        if r["session"] != prev_session and prev_session is not None:
            lines.append("")
        prev_session = r["session"]
        base_tok = M(float(r["baseline_input_tokens"]) + float(r["baseline_output_tokens"]))
        prune_tok = M(float(r["pruned_input_tokens"]) + float(r["pruned_output_tokens"]))
        lines.append(fmt.format(
            r["session"], r["level"],
            r["baseline_requests"], r["baseline_correct"],
            base_tok,
            r["pruned_requests"], r["pruned_correct"],
            prune_tok,
            r["correct_lost"], pct(r["correct_retention(%)"]),
        ))
    return "\n".join(lines)


def print_summary_table(summary_path: Path):
    with open(summary_path, newline="") as f:
        rows = list(csv.DictReader(f))
    table = render_table(rows)
    print(f"\n{table}")
    txt_path = summary_path.with_suffix(".txt")
    txt_path.write_text(table + "\n")
    print(f"✅ Table saved to {txt_path}")


def main():
    summary_path = Path("rq1/summary.csv")
    detail_path  = Path("rq1/bug_details.csv")
    summary_path.parent.mkdir(parents=True, exist_ok=True)

    summary_fieldnames = [
        "session", "level",
        "baseline_requests", "baseline_correct",
        "baseline_input_tokens", "baseline_output_tokens",
        "pruned_requests", "pruned_correct",
        "pruned_input_tokens", "pruned_output_tokens",
        "correct_lost", "correct_retention(%)",
    ]
    detail_fieldnames = [
        "bug", "session", "level",
        "total_aps",
        "baseline_requests", "baseline_correct",
        "pruned_requests", "pruned_correct",
        "request_reduction",
    ]

    with open(summary_path, "w", newline="") as sf, \
         open(detail_path,  "w", newline="") as df:
        summary_writer = csv.DictWriter(sf, fieldnames=summary_fieldnames)
        detail_writer  = csv.DictWriter(df, fieldnames=detail_fieldnames)
        summary_writer.writeheader()
        detail_writer.writeheader()
        for session in sessions:
            process_session(session, summary_writer, detail_writer)

    # Append aggregate rows to bug_details.csv
    numeric_cols = ["total_aps", "baseline_requests", "baseline_correct",
                    "pruned_requests", "pruned_correct", "request_reduction"]
    with open(detail_path, newline="") as df:
        detail_rows = list(csv.DictReader(df))

    # Group by (session, level) for meaningful aggregates
    from collections import defaultdict
    groups = defaultdict(list)
    for r in detail_rows:
        groups[(r["session"], r["level"])].append(r)

    with open(detail_path, "a", newline="") as df:
        writer = csv.DictWriter(df, fieldnames=detail_fieldnames)
        for (session, level), rows in sorted(groups.items()):
            for stat, fn in [("SUM", sum), ("MAX", max), ("AVG", lambda vals: round(sum(vals)/len(vals), 2)), ("MIN", min)]:
                agg = {"bug": stat, "session": session, "level": level}
                for col in numeric_cols:
                    vals = [float(r[col]) for r in rows]
                    agg[col] = fn(vals)
                writer.writerow(agg)

    print(f"\n✅ Summary saved to {summary_path}")
    print(f"✅ Bug details saved to {detail_path}")
    print_summary_table(summary_path)


if __name__ == "__main__":
    main()
