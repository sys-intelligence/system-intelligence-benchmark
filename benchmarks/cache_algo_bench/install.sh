#!/bin/bash

set -e  # Exit immediately on error.

if ! command -v uv >/dev/null 2>&1; then
    echo "==> uv not found. Installing uv..."
    curl -LsSf https://astral.sh/uv/install.sh | sh
    export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$PATH"
fi

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
export UV_CACHE_DIR="${UV_CACHE_DIR:-${REPO_ROOT}/.uv-cache}"

# install tools
echo "==> Installing tools for CacheBench..."
# cd scripts && bash install_dependency.sh && bash install_libcachesim.sh

# if .venv does not exist, create it
if [ -d ".venv" ]; then
    echo "==> .venv already exists, skipping creation."
else
    echo "==> Creating .venv directory..."
    uv venv .venv
fi

uv sync --extra dev

echo "==> CacheBench environment is set up successfully."
