#!/bin/bash
set -e

echo "=== Evaluation ==="

cd /workspace

export PATH=$PATH:/usr/local/go/bin

echo "Verifying protected files were not modified"
PROTECTED_FILES=(
    "src/kvraft/config.go"
    "src/kvraft/test_test.go"
)

for file in "${PROTECTED_FILES[@]}"; do
    if [ -f "$file" ] && [ -f "/tmp/checksums/$(basename $file).sha256" ]; then
        echo "  Checking $file"
        sha256sum -c "/tmp/checksums/$(basename $file).sha256" || {
            echo "FAIL: $file was modified"
            exit 1
        }
    fi
done
echo "All protected files unchanged"

echo "Running KVRaft 4A tests"
cd src/kvraft
go test -run 4A -race

if [ $? -eq 0 ]; then
    echo "PASS: Tests passed"
    exit 0
else
    echo "FAIL: Tests failed"
    exit 1
fi
