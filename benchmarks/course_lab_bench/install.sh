#!/bin/bash

set -e  # Exit immediately on error.

docker --version
python3.12 -m venv .venv
# python3 -m venv .venvdoc
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

pip install -r requirements.txt
pip install pytest
pip install pytest-cov
deactivate

echo "==> Setting up CourseLabBench environment..."
cd data/benchmark/projects
if [ -d "test-repo" ]; then
    echo "==> test-repo already exists, skipping clone."
else
    echo "==> Cloning test-repo... "
    git clone https://github.com/SWE-agent/test-repo.git
fi

if [ -d "6.5840-golabs-2024" ]; then
    echo "==> 6.5840-golabs-2024 already exists, skipping clone."
else
    echo "==> Cloning 6.5840-golabs-2024..."
    git clone git://g.csail.mit.edu/6.5840-golabs-2024
fi

if [ -d "xv6-labs-2024" ]; then
    echo "==> xv6-labs-2024 already exists, skipping clone."
else
    echo "==> Cloning xv6-labs-2024..."
    git clone git://g.csail.mit.edu/xv6-labs-2024
fi

if [ -d "6.5840-golabs-2025" ]; then
    echo "==> 6.5840-golabs-2025 already exists, skipping clone."
else
    echo "==> Cloning 6.5840-golabs-2025..."
    git clone git://g.csail.mit.edu/6.5840-golabs-2025
fi

echo "==> CourseLabBench environment is set up successfully."
