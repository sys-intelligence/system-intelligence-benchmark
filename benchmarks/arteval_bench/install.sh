#!/bin/bash

set -e  # Exit immediately on error.

# if .venv does not exist, create it
if [ -d ".venv" ]; then
    echo "==> .venv already exists, skipping creation."
else
    echo "==> Creating .venv directory..."

    python3 -m venv .venv
    source .venv/bin/activate
    
    if [ ! -d "SWE-agent" ]; then
        echo "==> Install SWE-agent and its dependencies..."
        git clone https://github.com/SWE-agent/SWE-agent.git
        cd SWE-agent
        git checkout 0c27f286303a939aa868ad2003bc4b6776771791
        pip install --editable .
        sweagent --help
        cd ..
    else
        echo "==> SWE-agent repository already exists, skipping clone."
    fi
    
    deactivate
fi

echo "==> ArtEvalBench environment is set up successfully."
