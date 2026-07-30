#!/bin/bash

set -e

if ! command -v uv >/dev/null 2>&1; then
    echo "==> uv not found. Installing uv..."
    curl -LsSf https://astral.sh/uv/install.sh | sh
    export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$PATH"
fi

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
export UV_CACHE_DIR="${UV_CACHE_DIR:-${REPO_ROOT}/.uv-cache}"

# Create virtual environment
if [ ! -d ".venv" ]; then
    uv venv .venv
fi

# Install package dependencies declared in workspace pyproject.toml files
uv sync --extra dev

echo "✅ Installation complete. Virtual environment created in .venv/"
echo "👉 To activate: source .venv/bin/activate"
