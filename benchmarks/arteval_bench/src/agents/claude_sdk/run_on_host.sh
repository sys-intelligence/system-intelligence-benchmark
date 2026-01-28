#!/bin/bash
#
# Run Claude Agent SDK for artifact evaluation directly on host machine
# This avoids Docker-in-Docker issues with Kind clusters
#
# Usage:
#   ./run_on_host.sh                           # Use default Acto artifact
#   ./run_on_host.sh /path/to/artifact         # Specify artifact path
#   ./run_on_host.sh /path/to/artifact "task"  # Specify artifact and task
#
# Prerequisites:
#   - Docker installed and running
#   - Python 3.8+ with claude-agent-sdk installed
#   - ANTHROPIC_API_KEY environment variable set
#
# Optional (agent will install if needed):
#   - Go 1.18+
#   - Kind
#   - kubectl
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Check for API key
if [ -z "$ANTHROPIC_API_KEY" ]; then
    echo "ERROR: ANTHROPIC_API_KEY environment variable is not set."
    echo "Please set it: export ANTHROPIC_API_KEY='your-api-key'"
    exit 1
fi

# Check Docker is running
if ! docker ps &>/dev/null; then
    echo "ERROR: Docker is not running or not accessible."
    echo "Please start Docker first."
    exit 1
fi

# Install claude-agent-sdk if not available
if ! python3 -c "import claude_agent_sdk" &>/dev/null; then
    echo "Installing claude-agent-sdk..."
    # Try different methods for different systems
    if pip3 install claude-agent-sdk 2>/dev/null; then
        echo "Installed using pip3"
    elif pip3 install --user claude-agent-sdk 2>/dev/null; then
        echo "Installed using pip3 --user"
    elif pip3 install --break-system-packages claude-agent-sdk 2>/dev/null; then
        echo "Installed using pip3 --break-system-packages"
    elif pipx install claude-agent-sdk 2>/dev/null; then
        echo "Installed using pipx"
    else
        echo "ERROR: Failed to install claude-agent-sdk."
        echo "Please install it manually:"
        echo "  pip3 install --user claude-agent-sdk"
        echo "  OR"
        echo "  pip3 install --break-system-packages claude-agent-sdk"
        exit 1
    fi
fi

# Set environment variables for long timeout
export BASH_MAX_TIMEOUT_MS=172800000
export BASH_DEFAULT_TIMEOUT_MS=172800000
export PYTHONUNBUFFERED=1

# Parse arguments and run
if [ $# -eq 0 ]; then
    # Use default Acto artifact
    echo "Running with default Acto artifact..."
    python3 "$SCRIPT_DIR/run_on_host.py" --use-acto-default
elif [ $# -eq 1 ]; then
    # Custom artifact path, default task
    echo "Running with artifact at: $1"
    python3 "$SCRIPT_DIR/run_on_host.py" --artifact-path "$1"
else
    # Custom artifact path and task
    echo "Running with artifact at: $1"
    echo "Task: $2"
    python3 "$SCRIPT_DIR/run_on_host.py" --artifact-path "$1" --task "$2"
fi
