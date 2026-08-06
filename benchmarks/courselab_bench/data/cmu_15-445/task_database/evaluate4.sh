#!/bin/bash
set -e

cd /workspace

# Verify test files weren't modified
echo "Verifying protected test files were not modified"
if ! sha256sum -c /tmp/checksums/test4_txn_timestamp.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/concurrency/txn_timestamp_test.cpp was modified"
    exit 1
fi
if ! sha256sum -c /tmp/checksums/test4_txn_scan.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/concurrency/txn_scan_test.cpp was modified"
    exit 1
fi
if ! sha256sum -c /tmp/checksums/test4_txn_executor.sha256 > /dev/null 2>&1; then
    echo "FAIL: test/concurrency/txn_executor_test.cpp was modified"
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
make -j$(nproc) txn_timestamp_test > /dev/null 2>&1
if ! ./test/txn_timestamp_test; then
    echo "FAIL: txn_timestamp_test failed"
    exit 1
fi

make -j$(nproc) txn_scan_test > /dev/null 2>&1
if ! ./test/txn_scan_test; then
    echo "FAIL: txn_scan_test failed"
    exit 1
fi

make -j$(nproc) txn_executor_test > /dev/null 2>&1
if ! ./test/txn_executor_test; then
    echo "FAIL: txn_executor_test failed"
    exit 1
fi

# Format check
echo ""
echo "=== Format Check ==="
make format > /dev/null 2>&1
if ! make check-clang-tidy-p4; then
    echo "FAIL: clang-tidy check failed"
    exit 1
fi

echo ""
echo "PASS: All checks passed"
exit 0

