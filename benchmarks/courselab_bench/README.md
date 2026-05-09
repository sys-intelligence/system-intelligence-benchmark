# Course Lab Benchmark
> [!IMPORTANT]  
> This folder is **archived** and merged into **[SysEduBench](https://github.com/sys-intelligence/sysedubench-public)**. Please see [**sysedubench-public**](https://github.com/sys-intelligence/sysedubench-public) for the latest version and contribute there.

Evaluate AI agents on systems programming lab assignments.

> Leaderboard hosted on HuggingFace Spaces: [sys-intelligence/leaderboard](https://huggingface.co/spaces/sys-intelligence/leaderboard)

```bash
pip install -e .

# Run all tasks
inspect eval courselab --model anthropic/claude-haiku-4-5

# Run specific tasks
inspect eval courselab --model anthropic/claude-haiku-4-5 \
  -T task_ids='["distributed_systems__echo_server"]'

# Run with custom parameters
inspect eval courselab --model anthropic/claude-haiku-4-5 \
  -T max_turns=50

# View results
inspect view

# For more fine-grained control, modify and run the evaluation script directly:
python run_eval.py

# Validate that tasks are solvable by running pre-defined solution scripts:
python run_solution_validation.py
```

## Task Structure

Each lab task requires the following files:

```
data/course_id/task_id/
├── config.json      # Task metadata and artifacts to capture
├── task.md          # Problem statement shown to the agent
├── compose.yaml     # Docker sandbox configuration
├── evaluate.sh      # Grading script (exit 0 = pass, non-zero = fail)
├── sol.sh           # Reference solution script to validate task solvability
├── preprocess.sh    # Optional: setup script run before agent starts
└── starter/         # Optional: starter files copied to workspace
    └── *.py
```

- `config.json`: Contains `instance_id`, `course_id`, `timeout_minutes`, and optional `artifacts` list (files to capture after evaluation)
- `task.md`: Problem description given to the agent
- `compose.yaml`: Docker sandbox specification
- `evaluate.sh`: Runs tests and returns exit code 0 for pass, non-zero for fail
- `sol.sh`: Reference solution script that validates the task is solvable (executable bash script)
- `preprocess.sh`: Optional setup script that runs before the agent starts (commonly used with `evaluate.sh` to verify test files remain unchanged via hashing)
- `starter/`: Optional directory containing starter files that are copied to the workspace with the same relative paths

See [`data/distributed_systems/task_1_echo_server/`](data/distributed_systems/task_1_echo_server/) for a complete example.

## Adding New Labs

1. Create task directory: `data/course_id/task_id/`
2. Update `data/courses.json` with course metadata
3. Add `config.json`, `task.md`, `compose.yaml`, and `evaluate.sh`
4. Optionally add `starter/` directory with skeleton code
5. Optionally add `preprocess.sh` for test file integrity checks
6. Add `sol.sh` as a reference solution script to validate task solvability (see note below)
7. Run tests to validate: `python -m pytest tests/test_data_schema.py -v`

> **Note on Solution Scripts**: Every task must have a `sol.sh` reference solution to verify solvability. If you prefer not to have your solution publicly available, submit the entire lab to the [private repository](https://github.com/sys-intelligence/system-intelligence-benchmark-private/) instead.
>
> **Note on Sandboxing**: Inspect AI offers multiple sandbox environments (Docker, Kubernetes, local, etc.). For simplicity, and because the majority of tasks won't require more than that, we currently expose a streamlined way to include tasks that use Docker sandboxing via `compose.yaml`. For more information regarding sandboxing and available environments in Inspect AI, see the [Sandboxing documentation](https://inspect.aisi.org.uk/sandboxing.html#environment-binding). If the lab you are adding requires a different sandboxing environment (e.g., Kubernetes), refer to the Inspect AI documentation.

## Best Practices

Tasks should be designed carefully and responsibly to ensure they are fair. Here are some best practices:

- Test with at least one agent: If you test with multiple agents and LLMs and no agent solves the task, it's likely the task needs revision. Review the trajectories to understand whether failures have something in common.
- Pin git commits for reproducibility: When cloning a git repository, specify the exact commit, then delete the `.git` directory to remove the full history.

## Using Custom Agents

To use a different agent, pass it to the `courselab()` function:

```python
from inspect_ai import eval
from inspect_ai.solver import basic_agent
from inspect_ai.tool import bash
from courselab import courselab

eval(
    courselab(agent=basic_agent(tools=[bash()])),
    model="openai/gpt-4"
)
```

See the [Inspect AI Agents documentation](https://inspect.ai-safety-institute.org.uk/agents.html) for more information.
