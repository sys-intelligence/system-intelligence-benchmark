#!/bin/bash

set -e

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
    echo "Usage: $0 <model_name> <agent>"
    echo "Example: $0 gpt-4o"
    echo "Example: $0 claude-3-5-sonnet-20241022"
    echo "Example: $0 gpt-4o trace_based"
    exit 1
fi

MODEL_NAME="$1"
AGENT="${2:-agent_based}"
NEW_MODEL_NAME="${MODEL_NAME//\//_}"

if [ ! -x ".venv/bin/python" ]; then
    echo "==> .venv is missing. Run ./install.sh first."
    exit 1
fi

echo "==> Start to run SysMoBench"
uv run --no-sync python -m src.main \
    --model_name "${MODEL_NAME}" \
    --agent "${AGENT}" \
    --max_iterations 3
