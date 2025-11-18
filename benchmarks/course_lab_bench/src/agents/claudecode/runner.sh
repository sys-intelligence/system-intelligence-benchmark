
#!/bin/bash

set -e  # Exit immediately on error.

# set the model and task as parameters
if [ $# -ne 2 ]; then
    echo "Usage: $0 <model_name> <task_description>"
    echo "Example: $0 claude-sonnet-4-5-20250929 \"set java env\""
    exit 1
fi

export ANTHROPIC_API_KEY="sk-XXXX"
claude -p "$2" --model "$1" --output-format json