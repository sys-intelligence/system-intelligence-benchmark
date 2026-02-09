#!/bin/bash
set -e

cd /workspace

# Verify test file wasn't modified
echo "Verifying protected files were not modified"
if ! sha256sum -c /tmp/checksums/test.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/primer/count_min_sketch_test.cpp was modified"
    exit 1
fi
echo "Protected files unchanged"

# Build
echo ""
echo "=== Building ==="
rm -rf build
mkdir build && cd build
cmake -DCMAKE_BUILD_TYPE=Debug .. > /dev/null 2>&1
if ! make -j$(nproc); then
    echo "FAIL: Build failed"
    exit 1
fi

# Run tests
echo ""
echo "=== Running Tests ==="
make -j$(nproc) count_min_sketch_test > /dev/null 2>&1
if ! ./test/count_min_sketch_test; then
    echo "FAIL: Tests failed"
    exit 1
fi

# Format check
echo ""
echo "=== Format Check ==="
make format > /dev/null 2>&1
if ! make check-clang-tidy-p0; then
    echo "FAIL: clang-tidy check failed"
    exit 1
fi

echo ""
echo "PASS: All checks passed"
exit 0
