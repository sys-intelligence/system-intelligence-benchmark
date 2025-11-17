# How to Port an Existing Benchmark

A guide for integrating mature, independently-developed benchmarks using `SysMoBench` as an example.


## Step 1: Choose Git Integration Method

**Git Subtree vs Submodule:**

When porting an existing benchmark, you need to decide how to integrate the upstream benchmark code into the framework repository (i.e., `system_intelligence_benchmark`). While both Git Subtree and Git Submodule can work, we recommend **Git Subtree** for most benchmark porting scenarios.

**Why Subtree over Submodule for Benchmarks:**
- **Atomic commits and consistency**: Subtree keeps all code in the main repository's Git object database, avoiding state synchronization issues between the parent repo and submodule HEAD. You can modify framework code and benchmark code in a single atomic commit, ensuring consistency across the entire codebase.
- **Bidirectional sync flexibility**: `git subtree pull --squash` cleanly integrates upstream updates while maintaining repository history, and `git subtree push` enables contributing patches back to upstream.
- **Fewer gotchas**: Submodules have many edge cases that can confuse contributors (see [this detailed analysis](https://blog.timhutt.co.uk/against-submodules/))

**When to use Subtree:**
- Benchmark is relatively stable (not updated daily)
- Repository size is acceptable (most benchmarks are <100MB)
- You want contributors to have a smooth onboarding experience

**When Submodule might be acceptable:**
- Upstream updates extremely frequently
- Benchmark codebase is very large (>500MB)
- You need strict separation between upstream and integration code


## Step 2: Add Upstream as Git Subtree

```bash
# Add remote
git remote add benchmark-upstream https://github.com/upstream/repo.git

# Add as subtree
git subtree add --prefix benchmarks/your_benchmark/benchmark_core \
    benchmark-upstream main --squash
```


## Step 3: Create Directory Structure

```
benchmarks/your_benchmark/
├── benchmark_core/         # Git Subtree (DO NOT manually edit)
├── src/                    # Bridge layer
│   ├── main.py             
│   ├── executor.py      
│   └── evaluator.py            
├── data/benchmark/
│   └── tasks.jsonl
├── env.toml                # Config template with "XXX" placeholders
├── requirements.txt        # -r benchmark_core/requirements.txt
├── install.sh
├── run.sh
└── README.md
```

## Step 4: Write Adapter Layer

Mature benchmarks already have end-to-end execution pipelines and SDKs. However, to unify LLM/agent configuration management across the framework and improve maintainability (see [Benchmark Abstraction](benchmark_abstract.md)), we need an **adapter layer** in `benchmarks/your_benchmark/src/` to bridge the upstream benchmark with the framework.

### 4.1 Integrate Model Config Manager

The framework provides a centralized model configuration manager. You may have two options to integrate it:

**Option 1: Replace upstream config manager (Recommended)**

Directly inject the framework's config into the upstream benchmark's initialization. This is the simplest and most stable approach.

```python
# src/main.py
import sys
from pathlib import Path

# Add paths
SDK_ROOT = Path(__file__).parent.parent.parent.parent
BENCHMARK_CORE = Path(__file__).parent.parent / "benchmark_core"
sys.path.insert(0, str(SDK_ROOT))
sys.path.insert(0, str(BENCHMARK_CORE))

# Inject framework config
from sdk.utils import set_llm_endpoint_from_config
set_llm_endpoint_from_config(str(Path(__file__).parent.parent / 'env.toml'))

# Now import upstream - it will use framework's LLM config
from tla_eval.config import get_configured_model
```

**SysMoBench example**: Directly replaces upstream's `models.yaml` by setting environment variables before importing upstream modules.

**Option 2: Map framework config to upstream config**

If the upstream config system cannot be replaced, map the framework's config to upstream's format at runtime. Implementation depends on your specific benchmark.


### 4.2 Separate Executor and Evaluator

Any benchmark can be abstracted into two sequential modules: **Executor** (generation/interaction) and **Evaluator** (scoring). Separating them improves code clarity and extensibility, and enables integrating more sophisticated executors without modifying evaluation logic.

**Executor**: Handles the generation or iterative correction workflow
- Example: SysMoBench runs multi-phase generation with iterative error correction
- Encapsulates retry logic, model calls, and intermediate outputs

**Evaluator**: Performs the final evaluation
- Example: SysMoBench runs TLC checks and verification
- Returns standardized scores and diagnostic information


### 4.3 Define Task Format

Convert the upstream task format to the framework's standard `tasks.jsonl` schema. This decouples task definitions from execution logic, enabling `main.py` to iterate over tasks programmatically without hardcoding task-specific details.

```jsonl
{"task_id": "task_1", "description": "...", "metadata": {}}
{"task_id": "task_2", "description": "...", "metadata": {}}
```


## Step 5: Complete Integration

Most remaining steps (testing, documentation, root-level integration) are identical to creating a custom benchmark. See [Creating New Benchmarks](custom_benchmark.md) for detailed guidelines.

**Porting-specific considerations:**

### 5.1 Manage Dependencies

Reference upstream dependencies in `requirements.txt`:

```txt
# requirements.txt
-r benchmark_core/requirements.txt
```

### 5.2 Create install.sh

Install upstream dependencies:

```bash
#!/bin/bash
set -e

# Install upstream system dependencies (e.g., Java for SysMoBench)
# ...

python3 -m venv .venv
source .venv/bin/activate

pip install -r requirements.txt

# Run upstream setup scripts
python3 benchmark_core/scripts/setup.py

deactivate
```

### 5.3 Configure .gitignore

Exclude upstream-generated files:

```gitignore
# Exclude upstream runtime artifacts
benchmark_core/lib/
benchmark_core/output/
benchmark_core/.venv/
```


### 5.4 Other Steps

- **Tests**: See [custom_benchmark.md - Testing](custom_benchmark.md#testing)
- **README**: Document upstream source, version, and attribution
- **Root integration**: Update `cli/run_all_local.sh`, `README.md`


## Sync with Upstream

**Update:**
```bash
git subtree pull --prefix benchmarks/your_benchmark/benchmark_core \
    benchmark-upstream main --squash
```

**Contribute back:**
```bash
git subtree push --prefix benchmarks/your_benchmark/benchmark_core \
    benchmark-upstream feature-branch
```

