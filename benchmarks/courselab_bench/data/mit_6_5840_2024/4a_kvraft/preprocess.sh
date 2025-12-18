#!/bin/bash
set -e

echo '=== Preprocessing 4A Kvraft ==='

cd /workspace


echo 'Creating checksums for protected files...'
PROTECTED_FILES=(
    "src/kvraft/config.go"
    "src/kvraft/test_test.go"
)

mkdir -p /tmp/checksums
for file in "${PROTECTED_FILES[@]}"; do
    if [ -f "$file" ]; then
        sha256sum "$file" > "/tmp/checksums/$(basename $file).$(dirname $file | tr '/' '_').sha256"
        echo "  $file"
    fi
done

echo ''
echo 'Preprocessing complete'
echo 'Agent should focus on implementing:'
echo '  - src/kvraft/client.go'
echo '  - src/kvraft/common.go'
echo '  - src/kvraft/server.go'

exit 0