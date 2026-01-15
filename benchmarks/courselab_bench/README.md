# Course Lab Benchmark

Evaluate AI agents on systems programming lab assignments.

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
```

## Task Structure

Each lab task requires the following files:

```
data/course_id/task_id/
├── config.json      # Task metadata and artifacts to capture
├── task.md          # Problem statement shown to the agent
├── compose.yaml     # Docker sandbox configuration
├── evaluate.sh      # Grading script (exit 0 = pass, non-zero = fail)
├── preprocess.sh    # Optional: setup script run before agent starts
└── starter/         # Optional: starter files copied to workspace
    └── *.py
```

- `config.json`: Contains `instance_id`, `course_id`, `timeout_minutes`, and optional `artifacts` list (files to capture after evaluation)
- `task.md`: Problem description given to the agent
- `compose.yaml`: Docker sandbox specification
- `evaluate.sh`: Runs tests and returns exit code 0 for pass, non-zero for fail
- `preprocess.sh`: Optional setup script that runs before the agent starts (commonly used with `evaluate.sh` to verify test files remain unchanged via hashing)
- `starter/`: Optional directory containing starter files that are copied to the workspace with the same relative paths

See [`data/distributed_systems/task_1_echo_server/`](data/distributed_systems/task_1_echo_server/) for a complete example.

## Adding New Labs

1. Create task directory: `data/course_id/task_id/`
2. Update `data/courses.json` with course metadata
3. Add `config.json`, `task.md`, `compose.yaml`, and `evaluate.sh`
4. Optionally add `starter/` directory with skeleton code
5. Optionally add `preprocess.sh` for test file integrity checks
6. Run tests to validate: `python -m pytest tests/test_data_schema.py -v`

> Note on Sandboxing: Inspect AI offers multiple sandbox environments (Docker, Kubernetes, local, etc.). For simplicity, and because the majority of tasks won't require more than that, we currently expose a streamlined way to include tasks that use Docker sandboxing via `compose.yaml`. For more information regarding sandboxing and available environments in Inspect AI, see the [Sandboxing documentation](https://inspect.aisi.org.uk/sandboxing.html#environment-binding). If the lab you are adding requires a different sandboxing environment (e.g., Kubernetes), refer to the Inspect AI documentation.

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
