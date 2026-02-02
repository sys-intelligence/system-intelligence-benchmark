#!/bin/bash
set -euo pipefail

echo "=== Setting up CMU 15-213 Bomb Lab ==="

cd /workspace

echo "Ensuring bomb assets are present"
required_files="bomb bomb.c README.bomb"
for file in $required_files; do
    if [ ! -f "$file" ]; then
        echo "ERROR: Missing required starter file: $file"
        exit 1
    fi
    echo "  ✓ $file"
done

# Install debugging essentials (gcc:12 is minimal)
echo "Installing debugging tools (gdb, binutils, procps, file)"
apt-get update
apt-get install -y gdb binutils procps file

# Provide a working solution file if the agent wants to edit in place
if [ ! -f solution.txt ]; then
    touch solution.txt
fi

# Make sure the bomb binary is executable
chmod +x bomb

# Record checksums to protect reference artifacts
mkdir -p /tmp/checksums
sha256sum bomb bomb.c README.bomb > /tmp/checksums/protected.sha256

echo "Bomb Lab setup complete. Use gdb/objdump/strings to recover all six inputs and write them to solution.txt."
