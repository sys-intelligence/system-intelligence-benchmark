# SpecFS Benchmark

## Scenario Description

Formal specifications are a cornerstone of building trustworthy systems software — particularly file systems, where subtle correctness bugs can cause data loss or security breaches. SpecFS Bench evaluates whether LLMs can translate structured, Hoare-logic-style specifications of file system modules into correct, modular C implementations that match expert-written ground truth.

### Task Details

- **Input**
  - Specification files (`.spec`) from `data/spec/`
  - Generation / Judge prompt template
  - Generation / Judge Model
- **Output**
  - Generated C source file per spec under `outputs/<run>/generated/<relative_path>.c`
  - Per-case generation records (`generation_results.jsonl`)
  - Per-case judge verdicts (`judge_results.jsonl`)
  - Aggregated summary (`summary.json`)
- **Evaluation**
  - `LLM-as-a-judge`: compares generated code against ground-truth C code under the same spec, scoring functional equivalence on a 0–10 scale with verdict (`pass` / `partial` / `fail`), a short rationale, and a list of differences.

### Key Features

- Structured spec format combining natural-language intent with formal pre/post-conditions
- Modular generation: the model produces a single module while reusing pre-defined APIs from other modules listed in `[RELY]`
- Fully automated two-phase pipeline: code generation → LLM-based judging
- Configurable generation and judge models

## Benchmark Setup

### Prerequisites

- Python 3.9+
- LLM endpoint configured in `env.toml`

### Configuration

Copy the example config and fill in credentials:

```bash
cp env.toml.example env.toml
```

Edit `benchmarks/specfs/env.toml`:

```toml
[llm]
OPENAI_API_KEY = "your_key_here"
OPENAI_API_BASE = "your_url_here"
```

If no local `env.toml` is found, the benchmark falls back to the workspace-level `env.toml` one directory above, and finally to environment variables.

### Install Dependencies

```bash
cd benchmarks/specfs
./install.sh
```

This script creates `.venv/` and installs `benchmarks/specfs/requirements.txt`.

### Run the Benchmark

```bash
./run.sh <model_name>
```

The wrapper invokes `src/main.py`, which:

1. Discovers all `.spec` files under `data/spec/` recursively.
2. Generates a C implementation for each spec using the generation prompt.
3. Judges each generated file against the corresponding ground truth under `data/code/` using the judge prompt.
4. Writes results under:

```
outputs/specfsbench__<model>__judge_<judge_model>__<timestamp>/
├── generated/              # Generated C files mirroring data/spec/ layout
├── generation_results.jsonl
├── judge_results.jsonl
└── summary.json            # Aggregated stats and average score
```

## Evaluation Metrics

SpecFS Bench uses an LLM-as-a-judge protocol to score each generated module against the reference implementation under the same spec.

For every case, the judge receives the spec, the generated code, and the ground-truth code, and returns a structured JSON verdict:

```json
{
  "score": 0-10,
  "verdict": "pass" | "partial" | "fail",
  "summary": "short rationale",
  "differences": ["difference 1", "difference 2"]
}
```

Aggregated metrics can be found in `summary.json`.


## Project Structure

```
benchmarks/specfs/
├── data/
│   ├── spec/                    # Spec files (.spec) organized by category
│   └── code/                    # Ground-truth C implementations (mirrors data/spec/)
├── src/
│   ├── main.py                  # Entry point: discover → generate → judge → summarize
│   ├── evaluator.py             # LLM-as-a-judge evaluator
│   ├── genspec_prompt.md        # Prompt template for code generation
│   └── judge_prompt.md          # Prompt template for the LLM judge
├── tests/
├── logs/                        # Run and install logs
├── outputs/                     # Per-run outputs (generated code, jsonl, summary)
├── env.toml.example             # Example configuration
├── install.sh                   # Environment setup script
├── run.sh                       # Benchmark entry wrapper
├── requirements.txt
└── README.md
```
