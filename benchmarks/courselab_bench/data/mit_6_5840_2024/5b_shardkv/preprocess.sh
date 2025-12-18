#!/bin/bash
set -e

echo '=== Preprocessing 5B Shardkv ==='

cd /workspace


echo 'Creating checksums for protected files...'
PROTECTED_FILES=(
    "src/shardctrler/config.go"
    "src/shardctrler/test_test.go"
    "src/shardkv/config.go"
    "src/shardkv/test_test.go"
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
echo '  - src/shardctrler/client.go'
echo '  - src/shardctrler/common.go'
echo '  - src/shardctrler/server.go'
echo '  - src/shardkv/client.go'
echo '  - src/shardkv/common.go'
echo '  - src/shardkv/server.go'

exit 0