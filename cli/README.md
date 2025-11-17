# Benchmark-CLI: Command Line Interface for Benchmark Execution

The CLI component provides tools for running all benchmarks in both local and Docker-based environments. It handles benchmark orchestration, environment setup, and result collection.

## Overview

The CLI enables you to:
- Run individual benchmarks or execute all benchmarks sequentially
- Deploy benchmarks in isolated Docker containers or local environments
- Automatically collect and aggregate results from multiple benchmark runs
  
## Installation

### Setup Virtual Environment

Run the installation script to create a Python virtual environment and install dependencies:

```bash
cd cli
./install.sh
```

This will:
1. Create a Python 3.12 virtual environment in `.venv/`
2. Install required packages from `requirements.txt`
3. Prepare the CLI environment for execution

### Dependencies

The CLI requires the following packages (automatically installed via `install.sh`):

- `swe-rex==1.3.0` - Runtime execution framework
- `requests==2.32.4` - HTTP library
- `azure-identity==1.23.0` - Azure authentication
- `litellm==1.77.5` - Unified LLM interface

## Usage

### Running All Benchmarks Locally

Execute all benchmarks sequentially with the local runner:

```bash
./run_all_local.sh <model_name>
```

This script will:
1. Validate that a model name argument is provided.
2. Iterate through each benchmark directory, running `install.sh` and `run.sh <model_name>` when they exist.
3. Copy the benchmark outputs back into `cli/` for easy inspection.

### Running with Docker

Make sure the virtual environment remains active when invoking the shell wrapper. For benchmarks that require containerized execution:

```bash
cd cli
./run_docker.sh
```

This script manages Docker-based benchmark execution with proper cleanup and isolation.

#### Running a Single Benchmark

With the virtual environment active, use the Docker runner to execute a specific benchmark:

```bash
cd cli
# Activate the CLI virtual environment before running any commands:
source .venv/bin/activate
python docker_run.py --benchmark_name <benchmark_name> --model_name <model>
```

**Arguments:**
- `--benchmark_name` (required): Name of the benchmark to run (e.g., `cache_bench`, `course_exam_bench`)
- `--model_name` (optional): LLM model to use (default: `gpt-4o`)

**Example:**
```bash
python docker_run.py --benchmark_name cache_bench --model_name gpt-4o
```

## Configuration

Each benchmark includes an `env.toml` configuration file that specifies:

- **Hardware requirements**: GPU usage, memory limits
- **Docker settings**: Container image, entrypoint script
- **Environment variables**: API keys, endpoints

**Example `env.toml`:**
```toml
[llm]
OPENAI_API_KEY = "sk-XXXX"
AZURE_API_KEY = "XXX"
AZURE_API_BASE = "XXX"
AZURE_API_VERSION = "2024-05-01-preview"
ANTHROPIC_API_KEY = "sk-ant-XXXX"

[hardware]
use_gpu = false

[env-docker]
image = "default"  # or specify custom image
entrypoint = "run.sh"
```

**Supported Docker Images:**
- `default` - Maps to `xuafeng/swe-go-python:latest`
- Custom images can be specified directly

## Output Structure

Benchmark results are saved in timestamped directories:

```
cli/outputs/{benchmark_name}__{model_name}__{agent}_{timestamp}/
    avg_score.json      # Aggregated metrics
    result.jsonl        # Detailed results
```

### Output Files

- **`avg_score.json`**: Aggregate performance metrics (accuracy, scores, etc.)
- **`result.jsonl`**: Line-delimited JSON with detailed evaluation results for each test case
- **`logs/`**: Execution logs with timestamps

### Visualizing Results

Generate a visual leaderboard for any results directory with `dashboard.py`:

```bash
cd cli
python3 dashboard.py --results_dir outputs --output dashboard.html
```

The script produces `System Intelligence Leaderboard`, a dark-mode HTML report. See [example](dashboard.html) and screenshot below.

<img src="dashboard.png" alt="Dashboard Screenshot" width="600"/>

If Plotly is unavailable, the core leaderboard still renders while charts are omitted. Open the generated HTML file in a browser to explore the latest runs.

## Logging

The CLI uses a centralized logging system configured in `logger.py`:

- **Console output**: INFO level and above
- **File logging**: DEBUG level and above
- **Log files**: Stored in `cli/logs/vansys-cli_{date}.log`

**Log format:**
```
YYYY-MM-DD HH:MM:SS | LEVEL | logger-name | message
```

## Troubleshooting

### GPU Support

GPU support is currently not implemented. If a benchmark requires GPU and `use_gpu = true` in `env.toml`, the CLI will exit with an error message.

### Docker Issues

If Docker containers fail to start:
1. Ensure Docker is installed and running
2. Verify you have permission to run Docker commands (add user to `docker` group)
3. Check that the specified Docker image is available or can be pulled

### Virtual Environment Issues

If the virtual environment fails to activate:
```bash
cd cli
rm -rf .venv
./install.sh
```

## See Also

- [Main README](../README.md) - Project overview and benchmark descriptions
- [SDK Documentation](../sdk/) - Details on evaluators and LLM interfaces
- [Benchmark Examples](../benchmarks/example_bench/) - Template for creating new benchmarks
