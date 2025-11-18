#!/bin/bash

set -e  # Exit immediately on error.

if [ $# -ne 1 ]; then
    echo "Usage: $0 <model_name>"
    echo "Example: $0 claude-sonnet-4-5-20250929"
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
echo "==> Start to run CourseLabBench"
# Note that if you benchmark has multiple tasks, you need to add --task <task> 
# in your code to enable task selection.

python src/main.py \
    --agent "claudecode" \
    --model "$MODEL_NAME" \
    # --task "test"
    # --save_path "./outputs/course_lab_bench__${NEW_MODEL_NAME}__$(date +"%Y-%m-%d_%H-%M-%S")" \
    # --input_json "./data/benchmark/course_lab_task_examples.jsonl"

# python src/main_patch.py
    # --model "$MODEL_NAME" \
    # --save_path "./outputs/course_lab_bench__${NEW_MODEL_NAME}__$(date +"%Y-%m-%d_%H-%M-%S")" \

deactivate
