#!/bin/bash
set -e

echo "=== Preprocessing Raft Lab 3B ==="

cd /workspace

echo "Creating checksums for protected files"
PROTECTED_FILES=(
    "src/raft/config.go"
    "src/raft/persister.go"
    "src/raft/test_test.go"

)

mkdir -p /tmp/checksums
for file in "${PROTECTED_FILES[@]}"; do
    if [ -f "$file" ]; then
        sha256sum "$file" > "/tmp/checksums/$(basename $file).sha256"
        echo "  $file"
    fi
done



echo "Preprocessing complete"
exit 0
