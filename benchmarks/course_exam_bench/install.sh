#!/bin/bash

set -e  # Exit immediately on error.


if command -v sudo >/dev/null 2>&1; then
    sudo apt update 
    sudo apt install openjdk-17-jdk -y
else
    apt update
    apt install -y openjdk-17-jdk
fi


# Verify Java installation
readlink -f $(which java)

# Set JAVA_HOME environment variable
export JAVA_HOME=/usr/lib/jvm/java-17-openjdk-amd64
export PATH=$JAVA_HOME/bin:$PATH

# Verify JAVA_HOME
echo $JAVA_HOME
java -version

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

echo "==> CourseExamBench environment is set up successfully."