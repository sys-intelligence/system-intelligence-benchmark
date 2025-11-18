#!/bin/bash

set -e  # Exit immediately on error.

# install tools
echo "==> Installing tools for CacheBench..."
# cd scripts && bash install_dependency.sh && bash install_libcachesim.sh

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

echo "==> CacheBench environment is set up successfully."
