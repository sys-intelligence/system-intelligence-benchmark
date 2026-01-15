#!/bin/bash
set -e

echo "=== Evaluating ShardKV Lab 5A ==="

export PATH=$PATH:/usr/local/go/bin
cd /workspace/src

echo "Verifying protected files were not modified"
PROTECTED_FILES=(
    "src/shardctrler/config.go:config.go.src_shardctrler.sha256"
    "src/shardctrler/test_test.go:test_test.go.src_shardctrler.sha256"
    "src/shardkv/config.go:config.go.src_shardkv.sha256"
    "src/shardkv/test_test.go:test_test.go.src_shardkv.sha256"
)

for entry in "${PROTECTED_FILES[@]}"; do
    file="${entry%%:*}"
    checksum_name="${entry##*:}"
    if [ -f "$file" ] && [ -f "/tmp/checksums/${checksum_name}" ]; then
        if ! sha256sum -c "/tmp/checksums/${checksum_name}" > /dev/null 2>&1; then
            echo "FAIL: $file was modified"
            exit 1
        fi
    fi
done
echo "All protected files unchanged"

echo "Running ShardCtrler tests (up to 3 attempts)"
cd src/shardctrler

MAX_ATTEMPTS=3
for attempt in $(seq 1 $MAX_ATTEMPTS); do
    echo "ShardCtrler attempt $attempt of $MAX_ATTEMPTS"

    if timeout 600 go test -race 2>&1 | tee shardctrler_output.txt; then
        if grep -q "PASS" shardctrler_output.txt && ! grep -q "FAIL" shardctrler_output.txt; then
            echo "ShardCtrler tests passed"
            break
        fi
    fi

    if [ $attempt -lt $MAX_ATTEMPTS ]; then
        echo "ShardCtrler tests failed, retrying..."
        rm -f shardctrler_output.txt
        sleep 2
    else
        echo "FAIL: ShardCtrler tests failed after $MAX_ATTEMPTS attempts"
        exit 1
    fi
done

echo "Running ShardKV 5A tests (up to 3 attempts)"
cd ../shardkv

for attempt in $(seq 1 $MAX_ATTEMPTS); do
    echo "ShardKV 5A attempt $attempt of $MAX_ATTEMPTS"

    if timeout 600 go test -run 5A -race 2>&1 | tee test_output.txt; then
        if grep -q "PASS" test_output.txt && ! grep -q "FAIL" test_output.txt; then
            echo "PASS: All tests passed on attempt $attempt"
            exit 0
        else
            echo "Tests did not complete successfully on attempt $attempt"
        fi
    else
        echo "Test run timed out or failed on attempt $attempt"
    fi

    if [ $attempt -lt $MAX_ATTEMPTS ]; then
        echo "Cleaning up for retry..."
        rm -f test_output.txt 2>/dev/null || true
        sleep 2
    fi
done

echo "FAIL: Tests did not pass after $MAX_ATTEMPTS attempts"
exit 1
