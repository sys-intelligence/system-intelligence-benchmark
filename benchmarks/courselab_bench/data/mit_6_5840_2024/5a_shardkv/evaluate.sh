#!/bin/bash
set -e

echo "=== Evaluation ==="

cd /workspace

export PATH=$PATH:/usr/local/go/bin

echo "Verifying protected files were not modified"
PROTECTED_FILES=(
    "src/shardctrler/config.go:src_shardctrler_config.go"
    "src/shardctrler/test_test.go:src_shardctrler_test_test.go"
    "src/shardkv/config.go:src_shardkv_config.go"
    "src/shardkv/test_test.go:src_shardkv_test_test.go"
)

for entry in "${PROTECTED_FILES[@]}"; do
    file="${entry%%:*}"
    checksum_name="${entry##*:}"
    if [ -f "$file" ] && [ -f "/tmp/checksums/${checksum_name}.sha256" ]; then
        echo "  Checking $file"
        sha256sum -c "/tmp/checksums/${checksum_name}.sha256" || {
            echo "FAIL: $file was modified"
            exit 1
        }
    fi
done
echo "All protected files unchanged"

echo "Running ShardCtrler tests"
cd src/shardctrler
go test -race
if [ $? -ne 0 ]; then
    echo "FAIL: ShardCtrler tests failed"
    exit 1
fi

echo "Running ShardKV 5A tests"
cd ../shardkv
go test -run 5A -race

if [ $? -eq 0 ]; then
    echo "PASS: Tests passed"
    exit 0
else
    echo "FAIL: Tests failed"
    exit 1
fi
