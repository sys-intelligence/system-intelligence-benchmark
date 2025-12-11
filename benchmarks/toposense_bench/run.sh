#!/bin/bash

# ==============================================================================
# TopoSense-Bench Execution Script
#
# Usage:
#   ./run.sh [model_name]
#
# Examples:
#   ./run.sh "gpt-4o"                  # Run with OpenAI GPT-4o (Default)
#   ./run.sh "openai/deepseek-chat"    # Run with DeepSeek (via OpenAI-compatible endpoint)
#
# Note: Ensure that API keys are correctly configured in 'env.toml'.
# ==============================================================================

# Set default model to "gpt-4o" if no argument is provided
MODEL_NAME=${1:-"gpt-4o"}

echo "🚀 Starting TopoSense-Bench evaluation..."
echo "🤖 Model: $MODEL_NAME"

# Run the main evaluation script
python src/main.py --model_name "$MODEL_NAME"