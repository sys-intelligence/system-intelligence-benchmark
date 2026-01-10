#!/bin/bash
set -e

echo "=== Evaluating Data Lab ==="

# Step 0: Verify protected files were not modified
echo "Step 0: Verifying protected files integrity..."
if [ -f .protected_checksums ]; then
    if ! md5sum -c .protected_checksums > /dev/null 2>&1; then
        echo "FAIL: Protected files were modified!"
        echo "The following files should NOT be modified (only bits.c and bits.h can be edited):"
        md5sum -c .protected_checksums 2>&1 | grep -v "OK$" || true
        exit 1
    fi
    echo "Protected files integrity verified"
else
    echo "WARNING: No checksum file found, skipping integrity check"
fi

# Make sure dlc is executable
chmod +x dlc

# Step 1: Check coding rule compliance with dlc
echo "Step 1: Checking coding rule compliance with dlc..."
dlc_output=$(./dlc bits.c 2>&1) || {
    echo "FAIL: dlc detected coding rule violations:"
    echo "$dlc_output"
    exit 1
}

if [ -n "$dlc_output" ]; then
    echo "dlc warnings/errors:"
    echo "$dlc_output"
fi
echo "dlc check passed"

# Step 2: Build btest
echo "Step 2: Building btest..."
make clean > /dev/null 2>&1 || true
make_output=$(make btest 2>&1) || {
    echo "FAIL: Failed to compile btest"
    echo "Compilation output:"
    echo "$make_output"
    exit 1
}
echo "btest compiled successfully"

# Step 3: Run btest for correctness
echo "Step 3: Running btest..."
btest_output=$(./btest -g 2>&1)
btest_exit_code=$?

echo "btest output:"
echo "$btest_output"

# Parse btest output to check for failures
# btest -g output format: "Score  Rating  Errors  Function"
# A function passes if Errors is 0

# Check if all functions passed (no errors reported)
if echo "$btest_output" | grep -qE "ERROR|error|Error"; then
    echo "FAIL: btest detected errors in some functions"
    exit 1
fi

# Check total score
total_score=$(echo "$btest_output" | grep "Total points" | awk '{print $3}' | cut -d'/' -f1)
max_score=$(echo "$btest_output" | grep "Total points" | awk '{print $3}' | cut -d'/' -f2)

if [ -n "$total_score" ] && [ -n "$max_score" ]; then
    echo "Score: $total_score / $max_score"
    if [ "$total_score" = "$max_score" ]; then
        echo "PASS: All functions implemented correctly"
        exit 0
    else
        echo "FAIL: Not all functions implemented correctly (score: $total_score/$max_score)"
        exit 1
    fi
fi

# Fallback: check if btest exited with success
if [ $btest_exit_code -eq 0 ]; then
    echo "PASS: btest completed successfully"
    exit 0
else
    echo "FAIL: btest exited with code $btest_exit_code"
    exit 1
fi
