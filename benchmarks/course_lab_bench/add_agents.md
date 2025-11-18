# Adding a New Agent

To integrate a new agent into the benchmark, follow these steps:

## 1. Create Agent Directory

Create a new directory under `src/agents/` with your agent name:

```sh
mkdir src/agents/your_agent_name
cd src/agents/your_agent_name
```

## 2. Create Required Files

Each agent requires two files:

### `install.sh` (optional but recommended)

Installation script for your agent's dependencies:

```bash
#!/bin/bash
set -e  # Exit immediately on error.

# Install your agent's dependencies
# Example: pip install your-agent-package
# Example: npm install -g your-agent-cli
```

### `runner.sh` (required)

Execution script that accepts model and task parameters:

```bash
#!/bin/bash
set -e  # Exit immediately on error.

# Validate parameters
if [ $# -ne 2 ]; then
    echo "Usage: $0 <model_location> <task_description>"
    echo "Example: $0 azure/gpt-4 \"implement MapReduce\""
    exit 1
fi

# Set API keys (read from env.toml or environment variables)
export YOUR_API_KEY="your_key_here"

# Run your agent with the provided model and task
# $1 = model_location
# $2 = task_description
your-agent-command -m "$1" -t "$2" -o agent_trajectory.json
```

## 3. Agent Integration Points

Your agent runner will be executed in a Docker container with:

- **Working directory**: `/repo` (contains the project to work on)
- **Agent directory**: `/agent` (contains your install.sh and runner.sh)
- **Parameters**:
  - `$1`: Model name/location (e.g., `anthropic/claude-sonnet-4-5-20250929`)
  - `$2`: Task description (multi-line text describing what to implement)

## 4. Examples

### Claude Code Agent
```bash
# install.sh
apt-get update -y
apt-get install -y nodejs npm
npm install -g @anthropic-ai/claude-code

# runner.sh
export ANTHROPIC_API_KEY="sk-ant-..."
claude -p "$2" --model "$1" --output-format json
```

### OpenHands Agent
```bash
# install.sh
curl -sSL https://install.python-poetry.org | python3 -
export PATH="$HOME/.local/bin:$PATH"
git clone https://github.com/All-Hands-AI/OpenHands.git
cd OpenHands/
poetry install

# runner.sh
cd OpenHands/
poetry run python -m openhands.core.main \
  --config-file /agent/config.toml \
  --agent-cls CodeActAgent \
  --selected-repo /repo \
  -t "$2"
```

## 5. Testing Your Agent

1. Add your agent path to the evaluation script
2. Run the benchmark:
   ```sh
   python src/main.py --agent ./src/agents/your_agent_name
   ```

## 6. Best Practices

- Make scripts executable: `chmod +x install.sh runner.sh`
- Handle errors gracefully with `set -e`
- Use environment variables for API keys
- Output agent trajectory/logs for debugging
- Test with simple tasks first before running full benchmark
- Ensure your agent can work within the `/repo` directory context

## 7. Agent Execution Flow

The benchmark framework executes your agent as follows:

1. **Setup Phase**:
   - Docker container starts with base image `xuafeng/swe-go-python:latest`
   - Project files uploaded to `/repo`
   - Agent files uploaded to `/agent`
   - `/agent/install.sh` executed (if exists)

2. **Execution Phase**:
   - Runner script executed: `/agent/runner.sh "<model>" "<task>"`
   - Agent works in `/repo` directory
   - Agent should modify files to complete the task

3. **Evaluation Phase**:
   - Test method from task specification executed (e.g., `cd src/main && bash test-mr.sh`)
   - Results captured and saved to `outputs/`


## 8. Troubleshooting

### Common Issues

**Agent can't find dependencies**:
- Ensure `install.sh` installs all required packages
- Check Docker image has necessary base dependencies

**Permission denied errors**:
- Make scripts executable: `chmod +x install.sh runner.sh`
- Check file permissions in Docker container

**API key not found**:
- Set environment variables in `runner.sh`
- Alternatively, configure in `env.toml` and read from there

**Agent output not captured**:
- Ensure agent outputs to `agent_trajectory.json` or logs properly
- Check exit codes and error handling
