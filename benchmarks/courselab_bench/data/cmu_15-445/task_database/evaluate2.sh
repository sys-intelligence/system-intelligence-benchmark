#!/bin/bash
set -e

cd /workspace

# Verify test files weren't modified
echo "Verifying protected test files were not modified"
if ! sha256sum -c /tmp/checksums/test2_b_plus_tree_insert.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/storage/b_plus_tree_insert_test.cpp was modified"
    exit 1
fi
if ! sha256sum -c /tmp/checksums/test2_b_plus_tree_sequential_scale.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/storage/b_plus_tree_sequential_scale_test.cpp was modified"
    exit 1
fi
if ! sha256sum -c /tmp/checksums/test2_b_plus_tree_delete.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/storage/b_plus_tree_delete_test.cpp was modified"
    exit 1
fi
if ! sha256sum -c /tmp/checksums/test2_b_plus_tree_concurrent.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/storage/b_plus_tree_concurrent_test.cpp was modified"
    exit 1
fi
echo "Protected test files unchanged"

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
