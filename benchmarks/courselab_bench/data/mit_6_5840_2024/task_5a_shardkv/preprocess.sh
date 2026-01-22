#!/bin/bash
set -e

echo "=== Setting up ShardKV Lab 5A ==="

cd /workspace

echo "Installing git"
apt-get update > /dev/null 2>&1
apt-get install -y git > /dev/null 2>&1

echo "Cloning 6.5840 lab repository"
git clone git://g.csail.mit.edu/6.5840-golabs-2024 /tmp/lab-repo > /dev/null 2>&1

echo "Moving src directory to workspace"
mv /tmp/lab-repo/src ./src


echo "Removing git history"
rm -rf /tmp/lab-repo

echo "Cloning reference solutions"
git clone --depth 1 https://github.com/GaryHo34/MIT-6.5840-distributed-systems-labs.git /tmp/reference-solutions > /dev/null 2>&1

echo "Copying starter files from reference solutions"
cp -r /tmp/reference-solutions/src/mr src/
cp -r /tmp/reference-solutions/src/kvsrv src/
cp -r /tmp/reference-solutions/src/raft src/
cp -r /tmp/reference-solutions/src/kvraft src/

echo "Cleaning up reference solutions"
rm -rf /tmp/reference-solutions

cd src

echo "Verifying starter files were copied correctly"
STARTER_FILES=(
    "raft/raft.go"
    "kvraft/server.go"
    "kvsrv/server.go"
    "mr/coordinator.go"
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
    "shardctrler/config.go"
    "shardctrler/test_test.go"
    "shardkv/config.go"
    "shardkv/test_test.go"
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
