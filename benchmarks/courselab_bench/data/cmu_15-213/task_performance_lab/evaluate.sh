#!/bin/bash
# evaluate.sh - Grading script for Performance Lab
# Exit 0 = pass, non-zero = fail
set -e

cd /workspace

# Verify infrastructure files haven't been tampered with
if ! sha256sum -c .infrastructure.sha256 > /dev/null 2>&1; then
    echo "FAIL: Infrastructure files were modified. Only kernels.c should be changed."
    exit 1
fi

# Build the project
make clean
if ! make 2>&1; then
    echo "FAIL: Build failed. Check kernels.c for compilation errors."
    exit 1
fi

# Run driver in autograder mode with team check skipped
# Timeout after 120 seconds to prevent infinite loops
OUTPUT=$(timeout 120 ./driver -tg 2>&1) || true

# Check for correctness failures
if echo "$OUTPUT" | grep -qi "failed correctness"; then
    echo "FAIL: Correctness check failed"
    echo "$OUTPUT"
    exit 1
fi

# Check for fatal errors
if echo "$OUTPUT" | grep -qi "fatal error"; then
    echo "FAIL: Fatal error during benchmarking"
    echo "$OUTPUT"
    exit 1
fi

# Parse bestscores line: "bestscores:X.X:Y.Y:"
SCORES_LINE=$(echo "$OUTPUT" | grep "bestscores:" | head -1)
if [ -z "$SCORES_LINE" ]; then
    echo "FAIL: Could not parse benchmark scores"
    echo "$OUTPUT"
    exit 1
fi

ROTATE_SCORE=$(echo "$SCORES_LINE" | awk -F: '{print $2}')
SMOOTH_SCORE=$(echo "$SCORES_LINE" | awk -F: '{print $3}')

echo "Rotate speedup: $ROTATE_SCORE"
echo "Smooth speedup: $SMOOTH_SCORE"

# Check if scores meet threshold (1.5x speedup for both)
THRESHOLD=1.5
ROTATE_PASS=$(awk "BEGIN {print ($ROTATE_SCORE >= $THRESHOLD) ? 1 : 0}")
SMOOTH_PASS=$(awk "BEGIN {print ($SMOOTH_SCORE >= $THRESHOLD) ? 1 : 0}")

if [ "$ROTATE_PASS" -eq 1 ] && [ "$SMOOTH_PASS" -eq 1 ]; then
    echo "PASS: Both rotate ($ROTATE_SCORE) and smooth ($SMOOTH_SCORE) exceed ${THRESHOLD}x speedup"
    exit 0
else
    echo "FAIL: Insufficient speedup. Rotate=$ROTATE_SCORE (need >= $THRESHOLD), Smooth=$SMOOTH_SCORE (need >= $THRESHOLD)"
    exit 1
fi
