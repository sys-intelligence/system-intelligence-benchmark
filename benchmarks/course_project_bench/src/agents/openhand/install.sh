#!/bin/bash

set -e  # Exit immediately on error.
curl -sSL https://install.python-poetry.org | python3 -
# Make sure ~/.local/bin is on PATH for your shell session:
export PATH="$HOME/.local/bin:$PATH"

python -V  # should show 3.12.7
apt-get update -y
apt-get install -y tmux

pip install --no-cache-dir playwright && python -m playwright install --with-deps chromium

git clone https://github.com/All-Hands-AI/OpenHands.git
cd OpenHands/
poetry env use $(command -v python3.12)
poetry run python -V
poetry install