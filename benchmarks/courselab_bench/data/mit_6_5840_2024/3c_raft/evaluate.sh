#!/bin/bash
set -e

echo "=== Evaluation ==="

cd /workspace

export PATH=$PATH:/usr/local/go/bin

echo "Verifying protected files were not modified"
PROTECTED_FILES=(
    "src/raft/config.go"
    "src/raft/persister.go"
    "src/raft/test_test.go"

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

echo "Running Raft 3C tests"
cd src/raft
go test -run 3C -race

if [ $? -eq 0 ]; then
    echo "PASS: Tests passed"
    exit 0
else
    echo "FAIL: Tests failed"
    exit 1
fi
