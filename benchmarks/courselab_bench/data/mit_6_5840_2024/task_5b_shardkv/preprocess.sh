#!/bin/bash
set -e

echo "=== Setting up ShardKV Lab 5B ==="

cd /workspace

echo "Installing git"
apt-get update > /dev/null 2>&1
apt-get install -y git > /dev/null 2>&1

echo "Backing up starter files (previous lab solutions)"
if [ -d "raft" ] || [ -d "kvraft" ] || [ -d "kvsrv" ] || [ -d "mr" ]; then
    mkdir -p /tmp/starter_backup
    [ -d "raft" ] && cp -r raft /tmp/starter_backup/
    [ -d "kvraft" ] && cp -r kvraft /tmp/starter_backup/
    [ -d "kvsrv" ] && cp -r kvsrv /tmp/starter_backup/
    [ -d "mr" ] && cp -r mr /tmp/starter_backup/
else
    echo "ERROR: Starter files not found in /workspace"
    exit 1
fi

echo "Cloning 6.5840 lab repository"
git clone git://g.csail.mit.edu/6.5840-golabs-2024 src > /dev/null 2>&1

echo "Removing git history"
rm -rf src/.git

echo "Copying starter files into repository"
cp -r /tmp/starter_backup/* src/src/

cd src

echo "Verifying starter files were copied correctly"
STARTER_FILES=(
    "src/raft/raft.go"
    "src/kvraft/server.go"
    "src/kvsrv/server.go"
    "src/mr/coordinator.go"
)
for file in "${STARTER_FILES[@]}"; do
    if [ ! -f "$file" ]; then
        echo "ERROR: Starter file $file not found after copy"
        exit 1
    fi
    echo "  ✓ $file"
done

echo "Creating checksums for protected files"
PROTECTED_FILES=(
    "src/shardctrler/config.go"
    "src/shardctrler/test_test.go"
    "src/shardkv/config.go"
    "src/shardkv/test_test.go"
)

mkdir -p /tmp/checksums
for file in "${PROTECTED_FILES[@]}"; do
    if [ -f "$file" ]; then
        checksum_name="$(basename $file).$(dirname $file | tr '/' '_').sha256"
        sha256sum "$file" > "/tmp/checksums/$checksum_name"
        echo "  Protected: $file"
    fi
done

echo "Agent should implement:"
echo "  - src/shardctrler/client.go"
echo "  - src/shardctrler/common.go"
echo "  - src/shardctrler/server.go"
echo "  - src/shardkv/client.go"
echo "  - src/shardkv/common.go"
echo "  - src/shardkv/server.go"

echo "Setup complete"
