# System Intelligence SDK

Reusable SDK package for benchmark executors, evaluators, LLM access, and runtime utilities used by System Intelligence Benchmark.

Run the commands below from the repository root.

## Install (editable)

```bash
uv sync --extra dev
```

## Build

```bash
uv build --package system-intelligence-sdk --wheel --sdist
```

For CI-backed packaging and release notes, see
`../doc/sdk_packaging.md`.

## Package Contents
- `sdk.executor`: base and simple executors
- `sdk.evaluator`: shared evaluators and LLM-based judges
- `sdk.llm`: LiteLLM wrapper
- `sdk.utils`: TOML config and endpoint setup helpers
- `sdk.logger`: shared logger config

## Compatibility
This package preserves the existing import path:

```python
from sdk.utils import set_llm_endpoint_from_config
```
