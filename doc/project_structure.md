# Project Structure (Canonical)

This document defines the canonical repository structure and ownership boundaries.

## Why
- Make `sdk` independently reusable and publishable.
- Keep benchmark execution unified while allowing benchmark-specific code.
- Reduce ad-hoc path hacks and duplicated shell logic.

## Current Top-Level Layout
- `benchmarks/`: benchmark implementations.
- `cli/`: orchestration scripts and utilities.
- `sdk/`: shared evaluator/executor/llm/utils modules.
- `doc/`: contributor and architecture docs.

## Target Layout (Incremental)
```text
system-intelligence-benchmark/
  pyproject.toml
  benchmarks/
    <bench_name>/
      src/
      tests/
      pyproject.toml
      run.sh (thin wrapper)
      install.sh (thin wrapper)
  cli/
    benchctl.py
    run_all_local.sh (delegates to benchctl)
  sdk/
    README.md
    __init__.py
    evaluator.py
    executor.py
    llm.py
    logger.py
    utils.py
  doc/
    project_structure.md
```

## Boundary Rules
- `sdk/` only contains reusable shared runtime code.
- `benchmarks/*` contain benchmark-specific task data and adapter entrypoints.
- `cli/benchctl.py` is the single orchestration entrypoint.
- Shell scripts remain compatibility wrappers only.
- Root `pyproject.toml` is the workspace source of truth (`tool.uv.workspace.members`) and keeps benchmark package metadata declarations (`tool.system_intelligence.benchmark_packages`).

## Dependency Rules
- Each benchmark has its own `pyproject.toml` and local `.venv`.
- Shared SDK dependencies are declared in root `pyproject.toml`.
- Runtime should prefer installed packages over modifying `sys.path`.

## Migration Order
1. Package `sdk` as standalone Python package.
2. Introduce benchmark registry and `benchctl` command surface.
3. Move benchmark install/run behavior behind `benchctl`.
4. Keep Dockerfile/DevContainer as wrappers over the same contract.

## Non-Goals (for structure stage)
- No benchmark logic rewrite.
- No data/task format change.
- No immediate removal of existing shell entrypoints.
