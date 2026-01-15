#!/bin/bash
set -e

echo "=== Setting up MapReduce Lab ==="

cd /workspace

echo "Installing git"
apt-get update > /dev/null 2>&1
apt-get install -y git > /dev/null 2>&1

echo "Cloning 6.5840 lab repository"
git clone git://g.csail.mit.edu/6.5840-golabs-2024 src > /dev/null 2>&1

echo "Removing git history"
rm -rf src/.git

cd src
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
        echo "  Protected: $file"
    fi
done

echo "Setup complete"
