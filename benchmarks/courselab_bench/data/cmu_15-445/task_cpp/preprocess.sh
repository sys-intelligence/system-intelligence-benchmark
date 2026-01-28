#!/bin/bash
set -e

echo "=== Setting up CMU 15-445 Database Lab ==="

cd /workspace

echo "Installing git"
apt-get update > /dev/null 2>&1
apt-get install -y git > /dev/null 2>&1

echo "Cloning bustub repository"
git clone https://github.com/cmu-db/bustub.git /tmp/bustub > /dev/null 2>&1
git -C /tmp/bustub checkout bd3912741c45370d5f9c7bef638452b10b140138 > /dev/null 2>&1

echo "Moving source to workspace"
mv /tmp/bustub/* ./
mv /tmp/bustub/.clang-format ./ 2>/dev/null || true
mv /tmp/bustub/.clang-tidy ./ 2>/dev/null || true

echo "Removing git history"
rm -rf /tmp/bustub
rm -rf .git

echo "Installing build dependencies"
build_support/packages.sh -y > /dev/null 2>&1

echo "Creating checksums for protected files"
PROTECTED_FILES=(
    "test/primer/count_min_sketch_test.cpp"
)

mkdir -p /tmp/checksums
for file in "${PROTECTED_FILES[@]}"; do
    if [ -f "$file" ]; then
        checksum_name="$(basename $file).sha256"
        sha256sum "$file" > "/tmp/checksums/$checksum_name"
        echo "  Protected: $file"
    fi
done

echo "Building project"
mkdir -p build
cd build
cmake -DCMAKE_BUILD_TYPE=Debug .. > /dev/null 2>&1
make -j$(nproc) > /dev/null 2>&1

echo "Agent should implement:"
echo "  - src/include/primer/count_min_sketch.h"
echo "  - src/primer/count_min_sketch.cpp"

echo "Setup complete"
