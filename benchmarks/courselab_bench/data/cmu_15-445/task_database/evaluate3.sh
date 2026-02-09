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
make -j$(nproc) sqllogictest > /dev/null 2>&1
if ! ./bin/bustub-sqllogictest ../test/sql/p3.00-primer.slt --verbose; then
    echo "FAIL: SQLLogicTest failed"
    exit 1
fi

# Format check
echo ""
echo "=== Format Check ==="
make format > /dev/null 2>&1
if ! make check-clang-tidy-p3; then
    echo "FAIL: clang-tidy check failed"
    exit 1
fi

echo ""
echo "PASS: All checks passed"
exit 0

