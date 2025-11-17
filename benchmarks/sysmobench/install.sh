#!/bin/bash

set -e

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
    python3 -m venv .venv
fi

source .venv/bin/activate

python -m pip install --upgrade pip
pip install -r requirements.txt

# Install sysmobench_core as editable so sysmobench/sysmobench-setup CLI entrypoints exist.
pip install -e sysmobench_core

# Download TLA+ tools (tla2tools.jar, CommunityModules, etc.).
echo "==> Downloading TLA+ tools..."
python3 sysmobench_core/tla_eval/setup_cli.py

deactivate

echo "==> SysMoBench environment is set up successfully."
