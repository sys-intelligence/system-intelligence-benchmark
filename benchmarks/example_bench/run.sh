#!/bin/bash

set -e  # Exit immediately on error.

if [ $# -ne 1 ]; then
    echo "Usage: $0 <model_location>"
    echo "Example: $0 Qwen/Qwen2.5-7B-Instruct"
    exit 1
fi

MODEL_NAME="$1"
NEW_MODEL_NAME="${MODEL_NAME//\//_}"

# Note: set it to "openai" if you are using your own model server (vllm)
# Otherwise, set it to "azure" if you are using azure gpt endpoint
# Run self-serving model
# export OPENAI_API_TYPE="openai"  
# export OPENAI_BASE_URL="http://localhost:2327/v1"
# export OPENAI_API_KEY="EMPTY"

source .venv/bin/activate
echo "==> Start to run ExampleBench"
# Note that if you benchmark has multiple tasks, you need to add --task <task> 
# in your code to enable task selection.
python src/main.py \
    --model_name "${MODEL_NAME}"
    # --save_path "./outputs/examplebench__${NEW_MODEL_NAME}__$(date +"%Y-%m-%d_%H-%M-%S")" \
    
deactivate
