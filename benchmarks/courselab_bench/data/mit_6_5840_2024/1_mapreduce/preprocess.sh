#!/bin/bash
set -e

echo "=== Preprocessing MapReduce Lab ==="

cd /workspace

echo "Creating checksums for protected files"
PROTECTED_FILES=(
    "src/main/mrcoordinator.go"
    "src/main/mrworker.go"
    "src/main/mrsequential.go"
    "src/main/test-mr.sh"
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
