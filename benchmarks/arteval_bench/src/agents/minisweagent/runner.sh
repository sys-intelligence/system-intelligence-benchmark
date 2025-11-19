#!/bin/bash

set -e  # Exit immediately on error.

# set the model and task as parameters
if [ $# -ne 2 ]; then
    echo "Usage: $0 <model_location> <task_description>"
    echo "Example: $0 azure/gpt-4.1 \"set java env\""
    exit 1
fi

pip install mini-swe-agent

export AZURE_API_KEY="XXXX"
export AZURE_API_BASE="XXXX"
export ANTHROPIC_API_KEY="sk-XXXX"


mini -t "$2" -m "$1" -y -o agent_trajectory.json
# mini -t "set java env" -m "anthropic/claude-sonnet-4-5-20250929" -y