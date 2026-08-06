#!/bin/bash
set -e

echo "=== Setting up CMU 15-445 CountMinSketch Lab ==="

cd /workspace

echo "Installing git"
apt-get update > /dev/null 2>&1
apt-get install -y git > /dev/null 2>&1

echo "Cloning bustub repository"
git clone https://github.com/cmu-db/bustub.git /tmp/bustub > /dev/null 2>&1

echo "Moving source to workspace"
mv /tmp/bustub/* ./
mv /tmp/bustub/.clang-format ./ 2>/dev/null || true
mv /tmp/bustub/.clang-tidy ./ 2>/dev/null || true
rm -rf /tmp/bustub .git

echo "Installing build dependencies"
build_support/packages.sh -y > /dev/null 2>&1

echo "Creating checksums for protected files"
mkdir -p /tmp/checksums
sha256sum test/primer/count_min_sketch_test.cpp > /tmp/checksums/test.sha256

echo "Building project"
mkdir -p build && cd build
cmake -DCMAKE_BUILD_TYPE=Debug .. > /dev/null 2>&1
make -j$(nproc) > /dev/null 2>&1

echo "Setup complete"
echo "Agent should implement:"
echo "  - src/include/primer/count_min_sketch.h"
echo "  - src/primer/count_min_sketch.cpp"
