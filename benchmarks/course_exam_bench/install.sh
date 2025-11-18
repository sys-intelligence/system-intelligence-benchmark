#!/bin/bash

set -e  # Exit immediately on error.

# Create virtual environment if it doesn't exist
if [ -d ".venv" ]; then
    echo "==> .venv already exists, skipping creation."
else
    echo "==> Creating .venv directory..."
    python3 -m venv .venv
    source .venv/bin/activate
    pip install --upgrade pip
    pip install -r requirements.txt
    pip install pytest pytest-cov
    deactivate
fi

echo "==> CourseExamBench environment is set up successfully."
