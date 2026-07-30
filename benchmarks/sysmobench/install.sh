#!/bin/bash

set -e

if ! command -v uv >/dev/null 2>&1; then
    echo "==> uv not found. Installing uv..."
    curl -LsSf https://astral.sh/uv/install.sh | sh
    export PATH="$HOME/.local/bin:$HOME/.cargo/bin:$PATH"
fi

REPO_ROOT="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
export UV_CACHE_DIR="${UV_CACHE_DIR:-${REPO_ROOT}/.uv-cache}"

# Ensure Java is available for TLA+ SANY/TLC.
if ! command -v java >/dev/null 2>&1; then
    echo "==> Java not found. Installing OpenJDK 17..."
    if command -v sudo >/dev/null 2>&1; then
        sudo apt update
        sudo apt install -y openjdk-17-jdk
    else
        apt update
        apt install -y openjdk-17-jdk
    fi
fi

readlink -f "$(which java)"
export JAVA_HOME=/usr/lib/jvm/java-17-openjdk-amd64
export PATH=$JAVA_HOME/bin:$PATH
java -version

echo "==> Installing SysMoBench dependencies..."

# Create (or reuse) the benchmark virtual environment.
if [ ! -d ".venv" ]; then
    echo "==> Creating .venv directory..."
    uv venv .venv
fi

uv sync --extra dev

# Install sysmobench_core as editable so sysmobench/sysmobench-setup CLI entrypoints exist.
source .venv/bin/activate
uv pip install -e sysmobench_core
deactivate

# Download TLA+ tools (tla2tools.jar, CommunityModules, etc.).
echo "==> Downloading TLA+ tools..."
uv run --no-sync python sysmobench_core/tla_eval/setup_cli.py

echo "==> SysMoBench environment is set up successfully."
