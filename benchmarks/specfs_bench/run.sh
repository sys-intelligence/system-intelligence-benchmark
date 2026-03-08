#!/bin/bash

set -e

if [ $# -lt 1 ] || [ $# -gt 2 ]; then
	echo "Usage: $0 <model_name> [judge_model_name]"
	echo "Example: $0 gpt-4o"
	echo "Example: $0 openai/deepseek-chat gpt-4o"
	exit 1
fi

MODEL_NAME="$1"
JUDGE_MODEL_NAME="${2:-$1}"

source .venv/bin/activate
echo "==> Running SpecFS benchmark"
echo "==> Generator model: ${MODEL_NAME}"
echo "==> Judge model: ${JUDGE_MODEL_NAME}"

python src/main.py \
	--model_name "${MODEL_NAME}" \
	--judge_model_name "${JUDGE_MODEL_NAME}"

deactivate

