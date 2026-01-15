#!/bin/bash
set -e

echo "=== Evaluating Raft Lab 3C ==="

export PATH=$PATH:/usr/local/go/bin
cd /workspace/src

echo "Verifying protected files were not modified"
PROTECTED_FILES=(
    "src/raft/config.go"
    "src/raft/persister.go"
    "src/raft/test_test.go"
)

for file in "${PROTECTED_FILES[@]}"; do
    if [ -f "$file" ] && [ -f "/tmp/checksums/$(basename $file).sha256" ]; then
        if ! sha256sum -c "/tmp/checksums/$(basename $file).sha256" > /dev/null 2>&1; then
            echo "FAIL: $file was modified"
            exit 1
        fi
    fi
done
echo "All protected files unchanged"

echo "Running Raft 3C tests (up to 3 attempts to handle timeouts)"
cd src/raft

MAX_ATTEMPTS=3
for attempt in $(seq 1 $MAX_ATTEMPTS); do
    echo "Attempt $attempt of $MAX_ATTEMPTS"

    if timeout 600 go test -run 3C -race 2>&1 | tee test_output.txt; then
        if grep -q "PASS" test_output.txt && ! grep -q "FAIL" test_output.txt; then
            echo "PASS: All tests passed on attempt $attempt"
            exit 0
        else
            echo "Tests did not complete successfully on attempt $attempt"
        fi
    else
        echo "Test run timed out or failed on attempt $attempt"
    fi

    # Clean up before retry
    if [ $attempt -lt $MAX_ATTEMPTS ]; then
        echo "Cleaning up for retry..."
        rm -f test_output.txt 2>/dev/null || true
        sleep 2
    fi
done

echo "FAIL: Tests did not pass after $MAX_ATTEMPTS attempts"
exit 1
