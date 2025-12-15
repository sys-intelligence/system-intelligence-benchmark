# Course Lab Benchmark

A benchmark for evaluating AI agents on systems programming labs. Agents run in Docker containers and are evaluated on their ability to complete course lab assignments.

We include a simple ReAct agent inspired by [mini-swe-agent](https://github.com/AUTOMATIC/mini-swe-agent).

## Quick Start

Make sure to export the appropriate API keys for your chosen model provider (copy `.env.toml.example` to `.env.toml` and fill in your keys). We use litellm for model access.

```bash
pip install -e .

# Prepare dataset (This will generate data/tasks.jsonl using the tasks in data/)
python prepare_dataset.py

# Run all tasks
python run_benchmark.py
```

## Usage

```bash
python run_benchmark.py \
  --tasks data/tasks.jsonl \
  --model anthropic/claude-sonnet-4-5-20250929 \
  --max-steps 50 \
  --max-cost 20.0
```

## Output

Each run creates a directory with a single `results.json` file:

```json
{
  "config": { "model": "...", "max_steps": 50, ... },
  "summary": {
    "total": 10,
    "passed": 8,
    "success_rate": 0.8,
    "total_cost": 0.234,
    "by_course": { "mit_6_5840_2024": { "total": 10, "passed": 8, ... } }
  },
  "results": [
    {
      "instance_id": "test__simple__echo",
      "passed": true,
      "agent_status": "completed",
      "test_output": "PASS: ...",
      "test_exit_code": 0,
      "duration_seconds": 12.5,
      "model_cost": 0.0033
    }
  ]
}
```

Detailed agent trajectories are saved in `trajectories/{instance_id}.jsonl`.

## Task Structure

Tasks are organized in a folder hierarchy:

```
data/
└── course_id/
    └── task_id/
        ├── config.json           # Task metadata
        ├── task.md               # Problem statement
        ├── preprocess.sh         # Setup script (runs before agent)
        └── evaluate.sh           # Evaluation script (determines pass/fail)
```

### config.json

Required fields:

- `instance_id`: Unique identifier (e.g., `"test__simple__echo"`)
- `course_id`: Course identifier (e.g., `"test_course"`)
- `docker_image`: Docker image to use (e.g., `"xuafeng/swe-go-python:latest"`)

Optional fields:

- `timeout_minutes`: Maximum execution time (default: 30)
- `tags`: List of topic tags
- `repo_url`: Git repository to clone
- `base_commit`: Git commit to checkout

### task.md

Markdown file containing the problem statement given to the agent.

### preprocess.sh

Shell script that runs before the agent starts. Use this to:

- Set up the environment
- If the lab depends on previous labs, copy reference implementations to prevent distractions
- Create checksums of files that shouldn't be modified
- Initialize test data

Exit with code 0 on success, non-zero on failure.

### evaluate.sh

Runs after the agent completes. Exit 0 for PASS, non-zero for FAIL.
Print verbose output for debugging (captured in results).

> The evaluation script is automatically retried up to 3 times or until a successful evaluation. This helps handle flaky tests or non-deterministic timeouts common in some systems programming labs.

### Example Task

See `data/test_course/test__simple__echo/` for a minimal example.

## Adding New Tasks

1. If you are adding tasks for a new course, first add a new entry to [`/data/courses.json`](./data/courses.json) with the course metadata
2. Create a new folder: `data/{course_id}/{task_id}/` (where `{course_id}` matches the entry in `courses.json`)
3. Add the 4 required files: `config.json`, `task.md`, `preprocess.sh`, `evaluate.sh` for each task
4. Make scripts executable
5. Run `python prepare_dataset.py` to regenerate `tasks.jsonl`
6. Run the benchmark
