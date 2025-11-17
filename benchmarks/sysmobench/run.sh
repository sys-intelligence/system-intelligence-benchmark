#!/bin/bash

set -e

if [ $# -ne 1 ]; then
    echo "Usage: $0 <model_name>"
    echo "Example: $0 gpt-4o"
    echo "Example: $0 claude-3-5-sonnet-20241022"
    exit 1
fi

MODEL_NAME="$1"
NEW_MODEL_NAME="${MODEL_NAME//\//_}"

# Activate venv if it exists
if [ -d ".venv" ]; then
    source .venv/bin/activate
fi

echo "==> Start to run SysMoBench"
python3 src/main.py \
    --model_name "${MODEL_NAME}" \
    --agent agent_based \
    --max_iterations 3

# Deactivate if we activated
if [ -d ".venv" ]; then
    deactivate
fi
