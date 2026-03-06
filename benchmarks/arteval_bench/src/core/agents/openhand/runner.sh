
#!/bin/bash

set -e  # Exit immediately on error.

# set the model and task as parameters
if [ $# -ne 2 ]; then
    echo "Usage: $0 <model_location> <task_description>"
    echo "Example: $0 azure/gpt-4.1 \"set java env\""
    exit 1
fi

if [ -z "${ANTHROPIC_API_KEY:-}" ]; then
    echo "ANTHROPIC_API_KEY is not set"
    exit 1
fi

echo "==> Start to run OpenHand Agent"
cd OpenHands/
poetry run python -m openhands.core.main --config-file /agent/config.toml --agent-cls CodeActAgent --selected-repo /repo -t "$2" --directory .
