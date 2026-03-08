# SpecFS-Bench

SpecFS-Bench evaluates LLM capability on **spec-to-code generation** for filesystem C functions.

The pipeline contains two stages:

1. **Generation**: For every `.spec` file under `data/spec`, ask the model to generate one corresponding C source file.
2. **Verification (LLM as Judge)**: Compare generated code against ground truth under `data/code` and output a simple score and diff summary.

## Data Layout

- `data/spec/**.spec`: formal function specifications and prompts.
- `data/code/**.c`: ground-truth implementation files (same relative path as spec, suffix changed to `.c`).

Example mapping:

- `data/spec/file/file_read.spec`
- `data/code/file/file_read.c`

## Installation

```bash
cd benchmarks/specfs_bench
./install.sh
```

## Configuration

Create `env.toml` in this benchmark directory (or use workspace-level `benchmarks/env.toml`).

You can copy from `env.toml.example` and fill your API credentials.

## Run

```bash
cd benchmarks/specfs_bench
./run.sh "gpt-4o"
# or use a separate judge model
./run.sh "openai/deepseek-chat" "gpt-4o"
```

## Outputs

Each run writes into `outputs/specfsbench__<model>__judge_<judge_model>__<timestamp>/`:

- `generated/`: generated `.c` files preserving spec relative path.
- `generation_results.jsonl`: per-spec generation status.
- `judge_results.jsonl`: per-file judge results (score, verdict, differences).
- `summary.json`: aggregate metrics.

