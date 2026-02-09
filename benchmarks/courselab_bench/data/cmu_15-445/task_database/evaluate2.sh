#!/bin/bash
set -e

cd /workspace

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
make -j$(nproc) b_plus_tree_insert_test > /dev/null 2>&1
if ! ./test/b_plus_tree_insert_test; then
    echo "FAIL: b_plus_tree_insert_test failed"
    exit 1
fi

make -j$(nproc) b_plus_tree_sequential_scale_test > /dev/null 2>&1
if ! ./test/b_plus_tree_sequential_scale_test; then
    echo "FAIL: b_plus_tree_sequential_scale_test failed"
    exit 1
fi

make -j$(nproc) b_plus_tree_delete_test > /dev/null 2>&1
if ! ./test/b_plus_tree_delete_test; then
    echo "FAIL: b_plus_tree_delete_test failed"
    exit 1
fi

make -j$(nproc) b_plus_tree_concurrent_test > /dev/null 2>&1
if ! ./test/b_plus_tree_concurrent_test; then
    echo "FAIL: b_plus_tree_concurrent_test failed"
    exit 1
fi

# Format check
echo ""
echo "=== Format Check ==="
make format > /dev/null 2>&1
if ! make check-clang-tidy-p2; then
    echo "FAIL: clang-tidy check failed"
    exit 1
fi

echo ""
echo "PASS: All checks passed"
exit 0
