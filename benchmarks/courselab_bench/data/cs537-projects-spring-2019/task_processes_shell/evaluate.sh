#!/bin/bash
set -e

echo "=== Evaluation ==="

cd /workspace/ostep-projects/processes-shell

echo "Verifying protected files were not modified"
if [ -f /tmp/checksums/protected.sha256 ]; then
  sha256sum -c /tmp/checksums/protected.sha256 || {
    echo "FAIL: Protected files were modified"
    exit 1
  }
fi
echo "All protected files unchanged"

echo "Running tests (up to 3 attempts to handle timeouts)"

MAX_ATTEMPTS=3
for attempt in $(seq 1 $MAX_ATTEMPTS); do
    echo "Attempt $attempt of $MAX_ATTEMPTS"

    # Clean previous build artifacts
    rm -f wish *.o 2>/dev/null || true

    echo "Building wish"
    if [ -f Makefile ]; then
        if timeout 300 make; then
            BUILD_SUCCESS=1
        else
            BUILD_SUCCESS=0
        fi
    else
        if timeout 300 gcc -D_GNU_SOURCE -std=gnu11 -Wall -Werror -O2 -o wish *.c; then
            BUILD_SUCCESS=1
        else
            BUILD_SUCCESS=0
        fi
    fi

    if [ $BUILD_SUCCESS -eq 0 ]; then
        echo "Build failed or timed out"
        if [ $attempt -lt $MAX_ATTEMPTS ]; then
            sleep 2
            continue
        else
            echo "FAIL: Build failed after $MAX_ATTEMPTS attempts"
            exit 1
        fi
    fi

    echo "Running tests"
    if timeout 600 bash test-wish.sh 2>&1 | tee test_output.txt; then
        echo "PASS: All tests passed on attempt $attempt"
        exit 0
    fi

    if [ $attempt -lt $MAX_ATTEMPTS ]; then
        echo "Tests failed, retrying..."
        rm -f test_output.txt 2>/dev/null || true
        sleep 2
    fi
done

echo "FAIL: Tests failed after $MAX_ATTEMPTS attempts"
exit 1
