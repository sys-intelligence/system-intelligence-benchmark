#!/bin/bash
set -euo pipefail

echo "=== Evaluating CMU 15-213 Bomb Lab ==="

cd /workspace
 
# Verify reference artifacts haven't been modified
if [ -f /tmp/checksums/protected.sha256 ]; then
    echo "Checking protected files"
    if ! sha256sum -c /tmp/checksums/protected.sha256; then
        echo "FAIL: Protected starter files were modified (bomb, bomb.c, README.bomb)"
        exit 1
    fi
fi

if [ ! -f solution.txt ]; then
    echo "FAIL: solution.txt not found. Write six input lines (one per bomb phase)."
    exit 1
fi

line_count=$(wc -l < solution.txt || echo 0)
if [ "$line_count" -lt 6 ]; then
    echo "FAIL: solution.txt must contain at least six lines (one per phase)."
    exit 1
fi

# Ensure the binary is executable
chmod +x bomb

echo "Running bomb with provided solution"
if ! timeout 120 ./bomb solution.txt > bomb_output.txt 2>&1; then
    echo "FAIL: bomb execution failed or timed out"
    cat bomb_output.txt || true
    exit 1
fi

echo "Checking bomb output"
if grep -q "BOOM!!!" bomb_output.txt; then
    echo "FAIL: Bomb exploded."
    cat bomb_output.txt
    exit 1
fi

if grep -q "Congratulations! You've defused the bomb!" bomb_output.txt; then
    echo "PASS: Bomb defused"
    exit 0
fi

echo "FAIL: Bomb did not report success"
cat bomb_output.txt
exit 1
