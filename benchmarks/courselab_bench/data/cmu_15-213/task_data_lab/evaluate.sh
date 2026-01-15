#!/bin/bash
set -e

echo "=== Evaluating Data Lab ==="

cd /workspace

echo "Verifying protected files were not modified"
if [ -f /tmp/checksums/protected.sha256 ]; then
    sha256sum -c /tmp/checksums/protected.sha256 || {
        echo "FAIL: Protected files were modified"
        echo "Only bits.c and bits.h can be edited"
        exit 1
    }
fi
echo "All protected files unchanged"

echo "Making dlc executable"
chmod +x dlc

echo "Running evaluation (up to 3 attempts to handle timeouts)"

MAX_ATTEMPTS=3
for attempt in $(seq 1 $MAX_ATTEMPTS); do
    echo "Attempt $attempt of $MAX_ATTEMPTS"

    # Clean previous build artifacts
    make clean > /dev/null 2>&1 || true

    # Step 1: Check coding rule compliance with dlc
    echo "Checking coding rule compliance with dlc"
    if timeout 300 ./dlc bits.c > dlc_output.txt 2>&1; then
        dlc_output=$(cat dlc_output.txt)
        if [ -n "$dlc_output" ]; then
            echo "dlc warnings/errors:"
            echo "$dlc_output"
            if echo "$dlc_output" | grep -q "ERROR"; then
                echo "FAIL: dlc detected coding rule violations"
                if [ $attempt -lt $MAX_ATTEMPTS ]; then
                    sleep 2
                    continue
                else
                    exit 1
                fi
            fi
        fi
        echo "dlc check passed"
    else
        echo "dlc check timed out"
        if [ $attempt -lt $MAX_ATTEMPTS ]; then
            sleep 2
            continue
        else
            echo "FAIL: dlc timed out after $MAX_ATTEMPTS attempts"
            exit 1
        fi
    fi

    # Step 2: Build btest
    echo "Building btest"
    if timeout 300 make btest > make_output.txt 2>&1; then
        echo "btest compiled successfully"
    else
        echo "FAIL: Failed to compile btest"
        cat make_output.txt
        if [ $attempt -lt $MAX_ATTEMPTS ]; then
            sleep 2
            continue
        else
            exit 1
        fi
    fi

    # Step 3: Run btest for correctness
    echo "Running btest"
    if timeout 600 ./btest -g > btest_output.txt 2>&1; then
        btest_output=$(cat btest_output.txt)
        echo "$btest_output"

        # Check if all functions passed
        if echo "$btest_output" | grep -qE "ERROR|error|Error"; then
            echo "FAIL: btest detected errors in some functions"
            if [ $attempt -lt $MAX_ATTEMPTS ]; then
                sleep 2
                continue
            else
                exit 1
            fi
        fi

        # Check total score
        total_score=$(echo "$btest_output" | grep "Total points" | awk '{print $3}' | cut -d'/' -f1 || echo "")
        max_score=$(echo "$btest_output" | grep "Total points" | awk '{print $3}' | cut -d'/' -f2 || echo "")

        if [ -n "$total_score" ] && [ -n "$max_score" ]; then
            echo "Score: $total_score / $max_score"
            if [ "$total_score" = "$max_score" ]; then
                echo "PASS: All functions implemented correctly on attempt $attempt"
                exit 0
            else
                echo "Not all functions implemented correctly (score: $total_score/$max_score)"
                if [ $attempt -lt $MAX_ATTEMPTS ]; then
                    sleep 2
                    continue
                else
                    echo "FAIL: Incomplete implementation after $MAX_ATTEMPTS attempts"
                    exit 1
                fi
            fi
        else
            echo "PASS: btest completed successfully on attempt $attempt"
            exit 0
        fi
    else
        echo "btest timed out or failed"
        if [ $attempt -lt $MAX_ATTEMPTS ]; then
            sleep 2
            continue
        else
            echo "FAIL: btest failed after $MAX_ATTEMPTS attempts"
            exit 1
        fi
    fi
done

echo "FAIL: Evaluation failed after $MAX_ATTEMPTS attempts"
exit 1
