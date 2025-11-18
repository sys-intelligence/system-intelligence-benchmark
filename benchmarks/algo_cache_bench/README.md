# Algorithm Design Benchmark - Cache [Under Development]

## Scenario Description

This benchmark evaluates the ability of AI models to design and implement efficient cache replacement policies. This benchmark challenges models to create custom eviction algorithms that minimize cache miss rates across diverse real-world workload traces, simulating practical cache optimization scenarios in storage systems and distributed computing environments.

### Task Details

Models are tasked with implementing a cache replacement policy that determines which objects to evict when the cache reaches capacity. The implementation must optimize for low miss rates while maintaining reasonable execution performance.

- **Input**:
  - System prompt defining the cache policy framework with accessible attributes
  - Cache snapshot data: `cache`, `size`, `capacity`, `access_count`, `hit_count`, `miss_count`
  - Object attributes: `key`, `size`
  - Workload traces from 6 different scenarios (alibaba-storage, ra-fwe, ra-multikey, tencentblock-storage, tmp, zipf)

- **Output**:
  - Python implementation with four required functions:
    - `evict(cache_snapshot, obj)`: Returns the key of the object to evict
    - `update_after_hit(cache_snapshot, obj)`: Updates metadata after a cache hit
    - `update_after_insert(cache_snapshot, obj)`: Updates metadata after inserting an object
    - `update_after_evict(cache_snapshot, obj, evicted_obj)`: Updates metadata after eviction

- **Evaluation**:
  - **Miss Rate**: Percentage of cache misses across all trace accesses (primary metric)
  - **Time Cost**: Average execution time in seconds
  - **Iterative Refinement**: Models undergo 3 rounds of feedback and refinement
  - Performance is measured against various workload patterns representing real-world scenarios

## Benchmark Setup

### Prerequisites

- Python 3.9+
- Virtual environment support
- LLM endpoint configured in `env.toml`

### Configuration

Edit `env.toml` to configure your LLM endpoint:

```toml
[llm]
AZURE_API_KEY = "your_api_key"
AZURE_API_BASE = "your_api_base_url"
AZURE_API_VERSION = "2024-05-01-preview"
ANTHROPIC_API_KEY = "your_anthropic_key"

[hardware]
use_gpu = false

[env-docker]
image = "default"
entrypoint = "./run.sh"
```

### Test in Docker

To test the benchmark in a Docker container:

1. Build the Docker image:

   ```sh
   docker build -t algo_cache_bench .
   ```

2. Run the container:

   ```sh
   docker run -it --rm algo_cache_bench
   ```

3. Inside the container, execute the benchmark:

   ```sh
   ./run.sh <model_name>
   ```

### Manual Test

#### Install Dependencies

Set up the environment and install necessary dependencies:

```sh
./install.sh
```

This script will:
- Create a Python virtual environment (`.venv`)
- Install required packages from `requirements.txt`
- Install pytest and pytest-cov for testing

#### Run the Benchmark

Execute the benchmark with a specific model and task:

```sh
./run.sh <model_name>
```

Example:
```sh
./run.sh Qwen/Qwen2.5-7B-Instruct
```

By default, the script runs the `alibaba-storage` task. To test other workload traces, modify `run.sh` to use different task options:
- `alibaba-storage`
- `ra-fwe`
- `ra-multikey`
- `tencentblock-storage`
- `tmp`
- `zipf`

#### Output

Results are saved in the `outputs/` directory with the following structure:

```
outputs/cachebench__<model>__<agent>__<task>__<timestamp>/
├── result.jsonl       # Detailed per-task results with responses
└── avg_score.json     # Average miss rate and time cost
```

Each result includes:
- Model response (implemented cache policy)
- Miss rate across all trace files
- Execution time cost
- Round-by-round refinement results
