# Course Lab Benchmark

A benchmark for evaluating AI agents on systems programming labs. We run agents in Docker containers and evaluate their ability to complete course lab assignments.

## Quick Start

Install dependencies:

```bash
pip install -e .
```

Configure your API keys by copying the example config at `.env.toml.example` to `.env.toml` and filling in your keys.

Run the benchmark on a set of tasks:

```bash
# Set your API key (supports any LiteLLM-compatible model)
export ANTHROPIC_API_KEY="your-key"  # or OPENAI_API_KEY, etc.

# Run benchmark
python run_benchmark.py --tasks data/tasks_lite.jsonl

# Evaluate results
python run_evaluation.py outputs/react_courselab_YYYYMMDD_HHMMSS
```

We include a simple ReAct agent inspired by [mini-swe-agent](https://github.com/AUTOMATIC/mini-swe-agent).

## Usage Options

```bash
python run_benchmark.py \
  --tasks data/tasks.jsonl \
  --model anthropic/claude-sonnet-4-5-20250929 \
  --max-steps 100 \
  --max-cost 10.0 \
  --agent react \
  --bench courselab
```

> replace `tasks` with `data/tasks_lite.jsonl` for a smaller set of tasks to test the setup.

## Output Structure

Each run creates a unique directory with all the data:

```
outputs/react_courselab_20241204_150530/
├── config.json                   # Run configuration
├── results_summary.json          # High-level stats
├── task_instance_1.json          # Individual task results
├── task_instance_2.json
├── trajectories/                 # Full conversation logs
│   ├── task_instance_1.jsonl
│   └── task_instance_2.jsonl
├── evaluations.json              # Detailed pass/fail per task
└── summary.json                  # Final scores and metrics
```

## How to Expand

### Adding Tasks

Add entries to `data/tasks.jsonl` (one JSON object per line):

```json
{
  "instance_id": "mit_6_5840_2024_raft_1",
  "course_id": "mit_6_5840_2024",
  "problem_statement": "Implement the Raft consensus algorithm...",
  "repo_url": "git://g.csail.mit.edu/6.5840-golabs-2024",
  "docker_image": "xuafeng/swe-go-python:latest",
  "install_commands": [],
  "test_command": "export PATH=$PATH:/usr/local/go/bin && cd src/raft && go test -race",
  "test_expected_substring": "PASS",
  "timeout_minutes": 30,
  "tags": ["distributed-systems", "raft", "consensus"]
}
```

**Required fields:**

- `instance_id`: Unique identifier (format: `{course_id}_{lab}_{task}`)
- `course_id`: Course identifier for grouping
- `problem_statement`: Instructions for the agent
- `docker_image`: Docker image to use
- `test_command`: Command to verify solution (include any env setup needed)
- `test_expected_substring`: String to look for in test output

**Optional fields:**

- `repo_url`: Git repository to clone
- `base_commit`: Git commit to checkout
- `install_commands`: Commands to run during setup
- `timeout_minutes`: Maximum execution time (default: 30)
- `tags`: List of topic tags

### Adding Courses

Add entries to `data/courses.json`:

```json
{
  "course_id": "mit_6_5840_2024",
  "name": "6.5840: Distributed Systems",
  "institution": "MIT",
  "year": 2024,
  "semester": "Spring",
  "topics": ["distributed systems", "consensus", "replication"],
  "course_url": "http://nil.csail.mit.edu/6.5840/2024/"
}
```
