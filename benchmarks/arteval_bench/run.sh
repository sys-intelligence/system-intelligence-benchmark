#!/bin/bash

set -e  # Exit immediately on error.

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
    echo "Usage: $0 <model_location> [agent]"
    echo "Example: $0 claude-sonnet-4-5-20250929 claude_sdk"
    echo "Example: $0 claude-sonnet-4-5-20250929 claudecode"
    echo "Note: agent defaults to 'claudecode' if not specified"
    exit 1
fi

MODEL_NAME="$1"
AGENT_NAME="${2:-claudecode}"  # Default to claudecode if not specified
NEW_MODEL_NAME="${MODEL_NAME//\//_}"

# Note: set it to "openai" if you are using your own model server (vllm)
# Otherwise, set it to "azure" if you are using azure gpt endpoint
# Run self-serving model
# export OPENAI_API_TYPE="openai"  
# export OPENAI_BASE_URL="http://localhost:2327/v1"
# export OPENAI_API_KEY="EMPTY"

source .venv/bin/activate
echo "==> Start to run ArtEvalBench"
echo "==> Model: $MODEL_NAME"
echo "==> Agent: $AGENT_NAME"

# Generate save path with timestamp
TIMESTAMP=$(date +"%Y-%m-%d_%H-%M-%S")
SAVE_PATH="./outputs/arteval_bench__${NEW_MODEL_NAME}__${AGENT_NAME}__${TIMESTAMP}"

# Run the benchmark
python src/main.py \
    --model_name "$MODEL_NAME" \
    --agent "$AGENT_NAME" \
    --save_path "$SAVE_PATH"

echo "==> Results saved to: $SAVE_PATH"

deactivate
