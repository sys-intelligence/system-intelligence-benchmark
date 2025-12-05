#!/bin/bash

set -e  # Exit immediately on error.

if [ $# -ne 1 ]; then
    echo "Usage: $0 <model_location>"
    echo "Example: $0 \"gemini/gemini-2.5-flash\""
    exit 1
fi

MODEL_NAME="$1"

source sregym_core/.venv/bin/activate

echo "==> Start to run SREGym"
python src/main.py \
    --agent "stratus" \
    --model_name "${MODEL_NAME}" 
    
deactivate
