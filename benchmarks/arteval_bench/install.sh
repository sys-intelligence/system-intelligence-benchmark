#!/bin/bash

set -e  # Exit immediately on error.

# if .venv does not exist, create it
if [ -d ".venv" ]; then
    echo "==> .venv already exists, skipping creation."
else
    echo "==> Creating .venv directory..."

    python3 -m venv .venv
    source .venv/bin/activate
    pip install -r requirements.txt
    pip install pytest
    pip install pytest-cov
    deactivate
fi

echo "==> ExampleBench environment is set up successfully."
