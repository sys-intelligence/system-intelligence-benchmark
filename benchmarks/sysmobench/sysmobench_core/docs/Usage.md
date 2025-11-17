# Usage Guide

## Command Structure

```bash
sysmobench --task <task> --method <method> --model <model> --metric <metric> [options]
```

### Required Parameters

- `--task` - System: `spin`, `mutex`, `rwmutex`, `etcd`, `redisraft`, `curp`, `dqueue`, `locksvc`, `raftkvs`
- `--method` - Generation method: `direct_call`, `agent_based`, `trace_based`
- `--model` - Model name (configured in `config/models.yaml`)

### Common Parameters

- `--metric` - Evaluation metric 
- `--spec-file <path>` - Use existing TLA+ spec (skip generation)
- `--config-file <path>` - Use existing TLC config (skip generation)

### Batch Evaluation

- `--tasks` - Multiple tasks (space-separated)
- `--metrics` - Multiple metrics
- `--output <dir>` - Output directory (default: `results/`)

### List Options

```bash
sysmobench --list-tasks
sysmobench --list-methods
sysmobench --list-models
sysmobench --list-metrics
```

## Metrics

SysMoBench evaluates models across **four dimensions**:

### 1. Syntax Correctness

| Metric | Description | Parameters |
|--------|-------------|------------|
| `compilation_check` | Full-model compilation with SANY | None |
| `action_decomposition` | Per-action validation with recovery | None |

### 2. Runtime Correctness

| Metric | Description | Parameters |
|--------|-------------|------------|
| `runtime_check` | Model checking without invariants | `--tlc-timeout <seconds>` |
| `coverage` | Action coverage via TLC statistics | `--tlc-timeout <seconds>` |
| `runtime_coverage` | Simulation-based coverage | `--tlc-timeout <seconds>` |

### 3. Conformance to Implementation

| Metric | Description | Applies To | Parameters |
|--------|-------------|------------|------------|
| `trace_validation` | Trace generation and validation | `spin`, `mutex`, `rwmutex`, `etcd`, `redisraft`, `curp` | `--with-exist-traces <N>`<br>`--with-exist-specTrace`<br>`--create-mapping` |
| `pgo_trace_validation` | Trace validation for PGo systems | `dqueue`, `locksvc`, `raftkvs` | `--with-exist-traces <N>` |

### 4. Invariant Correctness

| Metric | Description | Parameters |
|--------|-------------|------------|
| `invariant_verification` | Verify system-specific safety and liveness properties | `--tlc-timeout <seconds>` |

### Composite

| Metric | Description | Parameters |
|--------|-------------|------------|
| `composite` | Sequential evaluation across all dimensions | None |

## Model Configuration

### File Location
`config/models.yaml`

### Configuration Format

```yaml
models:
  <model_name>:
    provider: "openai" | "anthropic" | "genai" | "deepseek" | "yunwu"
    model_name: "<actual-model-name>"
    api_key_env: "<ENV_VAR_NAME>"
    temperature: <float>
    max_tokens: <int>
    timeout: <int>        # seconds, optional
    top_p: <float>        # optional
    url: "<endpoint>"     # optional, for custom endpoints
```

### Examples

```yaml
models:
  # Anthropic Claude
  claude:
    provider: "anthropic"
    model_name: "claude-sonnet-4-20250514"
    api_key_env: "ANTHROPIC_API_KEY"
    temperature: 0.1
    max_tokens: 64000
    top_p: 0.9
```

### Usage

1. Add model configuration to `config/models.yaml`
2. Set environment variable:
   ```bash
   export YOUR_API_KEY="key"
   ```
3. Use model name in command:
   ```bash
   sysmobench --task spin --method direct_call --model custom --metric compilation_check
   ```

## Output Structure

Results in `output/<metric>/<task>/<method>_<model>/`:

```
output/coverage/spin/direct_call_gemini/
├── generated_spec.tla
├── generated_config.cfg
├── evaluation_results.json
└── tlc_output.log
```

## Task Configuration

Task configs in `tla_eval/tasks/<task>/task.yaml`:

```yaml
name: "spin"
description: "Asterinas OS spinlock"
system_type: "concurrent"
language: "rust"

repository:
  url: "https://github.com/asterinas/asterinas.git"
  branch: "main"

source_files:
  - path: "ostd/src/sync/spin.rs"

default_source_file: "ostd/src/sync/spin.rs"
specModule: "spin"
traces_folder: "data/sys_traces/spin"
...
```
