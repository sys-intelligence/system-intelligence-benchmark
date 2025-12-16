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

source sregym_core/.venv/bin/activate

echo "==> Start to run SREGym"
python src/main.py \
    --agent "${AGENT_NAME}" \
    --model "${MODEL_ID}" 
    
deactivate
