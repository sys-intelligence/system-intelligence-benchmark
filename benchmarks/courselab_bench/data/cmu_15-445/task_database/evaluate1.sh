#!/bin/bash
set -e

cd /workspace

# Verify test files weren't modified
echo "Verifying protected test files were not modified"
if ! sha256sum -c /tmp/checksums/test1_arc_replacer.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/buffer/arc_replacer_test.cpp was modified"
    exit 1
fi
if ! sha256sum -c /tmp/checksums/test1_disk_scheduler.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/storage/disk_scheduler_test.cpp was modified"
    exit 1
fi
if ! sha256sum -c /tmp/checksums/test1_page_guard.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/buffer/page_guard_test.cpp was modified"
    exit 1
fi
if ! sha256sum -c /tmp/checksums/test1_buffer_pool_manager.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/buffer/buffer_pool_manager_test.cpp was modified"
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
make -j$(nproc) arc_replacer_test > /dev/null 2>&1
if ! ./test/arc_replacer_test; then
    echo "FAIL: Tests failed"
    exit 1
fi

make -j$(nproc) disk_scheduler_test > /dev/null 2>&1
if ! ./test/disk_scheduler_test; then
    echo "FAIL: Tests failed"
    exit 1
fi

make -j$(nproc) page_guard_test > /dev/null 2>&1
if ! ./test/page_guard_test; then
    echo "FAIL: Tests failed"
    exit 1
fi

make -j$(nproc) buffer_pool_manager_test > /dev/null 2>&1
if ! ./test/buffer_pool_manager_test; then
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