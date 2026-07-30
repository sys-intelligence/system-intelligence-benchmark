#!/bin/bash

set -e  # Exit immediately on error.

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
    echo "Usage: $0 <model_id> [agent_name]"
    echo "Example: $0 \"gpt-4o\""
    echo "Example: $0 \"gpt-4o\" \"stratus\""
    exit 1
fi

MODEL_ID="${1:-gpt-4o}"
AGENT_NAME="${2:-stratus}"  # Default to "stratus" if not provided

if [ ! -x "sregym_core/.venv/bin/python" ]; then
    echo "==> sregym_core/.venv is missing. Run ./install.sh first."
    exit 1
fi

export PYTHONPATH="$(pwd)/sregym_core:${PYTHONPATH:-}"

echo "==> Start to run SREGym"
uv run --python sregym_core/.venv/bin/python --no-sync python src/main.py \
    --agent_name "${AGENT_NAME}" \
    --model_name "${MODEL_ID}" 
