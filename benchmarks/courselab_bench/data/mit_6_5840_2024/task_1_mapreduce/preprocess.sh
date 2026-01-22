#!/bin/bash
set -e

echo "=== Setting up MapReduce Lab ==="

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

cd src
echo "Creating checksums for protected files"
PROTECTED_FILES=(
    "main/mrcoordinator.go"
    "main/mrworker.go"
    "main/mrsequential.go"
    "main/test-mr.sh"
)

mkdir -p /tmp/checksums
for file in "${PROTECTED_FILES[@]}"; do
    if [ -f "$file" ]; then
        sha256sum "$file" > "/tmp/checksums/$(basename $file).sha256"
        echo "  Protected: $file"
    fi
done

echo "Setup complete"
