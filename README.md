# SPRINT — Statically PRuning INfeasible Templates

**SPRINT** is a pruning technique that accelerates LLM-based Automated Program Repair (APR).
Given a buggy Java program and a set of fix templates, SPRINT prunes *infeasible* templates at the *partial program* level — before costly patch generation — by statically determining whether each partial program is *test-satisfiable* (i.e., can evolve into a complete program that passes the failing tests).
The test-satisfiability analysis combines a customized [Facebook Infer](https://fbinfer.com/) static checker with dynamic failing-test execution.

This artifact contains:
- The SPRINT analyzer (source code under `tool/sabfl/`)
- The LLM-based patch generation pipeline (`sprint/`, `experiment.py`)
- Pre-computed experiment data for two LLM sessions
- Scripts to reproduce all tables and figures from the paper (`experiment/rq*.py`)

---

## Repository Layout

```
FL4APR/
├── scripts/          # Per-bug analysis pipeline (prepare / trace / analyze / enum-ap)
│   ├── sprint.py     # Main per-bug CLI
│   ├── d4j.py        # Batch runner across all bugs
│   ├── bug.py        # Defects4J / Infer wrapper
│   └── config.py     # Path constants
├── sprint/           # LLM patch generation layer
│   ├── tgi/          # FastAPI backend + DB models (SQLModel + PostgreSQL)
│   └── scripts/      # CLI sub-commands (inference, export, convert)
├── tool/
│   ├── sabfl/        # SPRINT Infer checker (OCaml source; must be built)
│   ├── components/   # Java components (tracer, verifier)
│   └── validator/    # Patch validation scripts
├── experiment/       # Pre-computed data + RQ scripts
│   ├── rawdata/      # ap.json per bug per session
│   ├── patches/      # Generated patches with validation labels
│   ├── rq1.py        # RQ1: correctness vs. cost table
│   ├── rq2_compute.py# RQ2: budget curve computation
│   ├── rq2_plot.py   # RQ2: budget curve plot
│   ├── rq2.py        # RQ2: entry point (runs compute then plot)
│   └── rq3.py        # RQ3: pruning-rate histogram
├── app.py            # FastAPI server entry point (port 8001)
├── experiment.py     # Top-level CLI for all experiment commands
└── requirements.txt
```

---

## Requirements

| Component | Version |
|-----------|---------|
| Python    | 3.10+   |
| OCaml     | 4.14+   |
| Java      | 1.8     |
| PostgreSQL | 14+    |
| Defects4J | 2.0     |

**Python dependencies** (install in a virtualenv):
```bash
pip install -r requirements.txt
```

---

## Reproducing Paper Results (RQ1–RQ3)

Pre-computed data is already included under `experiment/`.
You only need Python + matplotlib installed.

```bash
cd experiment

# RQ1 — Table: correctness and cost with/without pruning
python3 rq1.py

# RQ2 — Figure: budget curve (# bugs fixed vs. # LLM queries)
python3 rq2.py          # generates rq2/curve_budget.png and rq2/compare_budget100.png

# RQ3 — Figure: pruning-rate histogram
python3 rq3.py          # generates rq3/histogram.png
```

Output files are written to `experiment/rq1/`, `experiment/rq2/`, and `experiment/rq3/`.

---

## Full Pipeline Setup (to re-run experiments from scratch)

### 1. Environment Variables

Export before running pipeline scripts:
```bash
export D4J_HOME=/path/to/defects4j-2.0
export TZ=America/Los_Angeles
```

Create a `.env` file at the repo root:
```
D4J_HOME=/path/to/defects4j-2.0
D4J_BUGS_DIR=/path/to/d4j_projects
GPT_HOST=https://api.openai.com
GPT_API_KEY=sk-...
BACKEND_URL=http://localhost:8001
```

### 2. Build the SPRINT Analyzer (Infer)

```bash
cd tool/sabfl
./build-infer.sh java -y
```

> **Note:** `build-infer.sh` uses `--solver=builtin-mccs+glpk`. If your opam installation reports a different default solver, edit that flag accordingly.

### 3. Build Java Components

```bash
cd tool/components
mvn -DskipTests install
```

### 4. Install Ant

`scripts/bug.py` requires `ant.1.10.15` (and `ant.1.8.4` for `Lang_*` bugs) as named
files under `$D4J_HOME/major/bin/`. Pre-built Ant 1.10.15 is included under `utils/`:

```bash
ln -s $(pwd)/utils/apache-ant-1.10.15/bin/ant $D4J_HOME/major/bin/ant.1.10.15
```

### 5. PostgreSQL Databases

The Python layer auto-creates tables, but the databases must be created manually:
```bash
sudo -u postgres psql -c "CREATE USER sprint WITH PASSWORD 'sprint';"
sudo -u postgres psql -c "CREATE DATABASE batch OWNER sprint;"
sudo -u postgres psql -c "CREATE DATABASE validator_db OWNER sprint;"
```

Connect with TCP auth: `psql -U sprint -d batch -h localhost`

### 6. OpenAI API Keys

Edit `sprint/tgi/initializer.py` and `sprint/scripts/sequential.py`, replacing the
`YOUR_OPENAI_API_KEY_HERE` placeholder with your actual key(s).

---

## Per-Bug Analysis Pipeline

Run from inside a checked-out Defects4J bug directory:

```bash
# Checkout bug
defects4j checkout -p Chart -v10b -w Chart_10
cd Chart_10

# Step 1: build + capture with Infer's frontend
python3 /path/to/FL4APR/scripts/sprint.py prepare

# Step 2: collect dynamic trace information
python3 /path/to/FL4APR/scripts/sprint.py trace

# Step 3: Test-SAT analysis
python3 /path/to/FL4APR/scripts/sprint.py analyze

# Step 4: enumerate abstract patches (writes convert_ir_patches.json)
python3 /path/to/FL4APR/scripts/sprint.py enum-ap
```

### Batch analysis across all bugs

Run from `scripts/`:
```bash
python3 d4j.py d4j-build   <bugs_dir>
python3 d4j.py capture      <bugs_dir>
python3 d4j.py tracer       <bugs_dir>
python3 d4j.py preanal      <bugs_dir>
python3 d4j.py analyze_bug_only <bugs_dir> --exnchecker
python3 d4j.py analyze_bug_only <bugs_dir>
python3 d4j.py enum-ap      <bugs_dir>
```

---

## LLM Patch Generation Pipeline

```bash
# Start FastAPI server (creates DB tables on first run)
python3 app.py &

# Register abstract patches into DB
python3 experiment.py register-abstract-patches register-baseline <bugs_dir>
python3 experiment.py register-abstract-patches register-baseline <bugs_dir> --pfl
python3 experiment.py register-abstract-patches mark-pruned <bugs_dir>

# Create experiment session
python3 experiment.py initialize-session --session_id my_session --model gpt-4.1

# Run inference (one worker process per API key)
python3 experiment.py sequential infer my_session

# Export patches to patches.json per bug
python3 experiment.py convert write-concrete-patches \
    --session-id my_session \
    --output patches/my_session
```

## Patch Validation

```bash
cd tool/validator

# Validate a single bug
python3 validator.py validate /path/to/d4j_projects/<bug_id> \
    /path/to/patches/<session>/<bug_id>/patches.json

# Validate all bugs in a session
python3 validator.py validate-all /path/to/patches/<session> /path/to/d4j_projects
```

## Export to Experiment Format

After validation, export diff files and labels:
```bash
python3 experiment.py export-sprint-format \
    --session-id <session_id> \
    --patches-dir patches/<session_id> \
    --bugs-dir /path/to/d4j_projects \
    --output-dir experiment
```

This writes:
- `experiment/patches/<session>/PFL/<bug>/<ap_id>/<cp_id>.diff`
- `experiment/rawdata/<session>/NFL/<bug>/ap.json`
