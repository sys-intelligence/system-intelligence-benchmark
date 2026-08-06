#!/bin/bash
set -e

echo "=== Setting up CMU 15-445 Database Lab ==="

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

echo "Creating checksums for protected test files"
mkdir -p /tmp/checksums
# Task 1 test files
sha256sum test/buffer/arc_replacer_test.cpp > /tmp/checksums/test1_arc_replacer.sha256
sha256sum test/storage/disk_scheduler_test.cpp > /tmp/checksums/test1_disk_scheduler.sha256
sha256sum test/buffer/page_guard_test.cpp > /tmp/checksums/test1_page_guard.sha256
sha256sum test/buffer/buffer_pool_manager_test.cpp > /tmp/checksums/test1_buffer_pool_manager.sha256
# Task 2 test files
sha256sum test/storage/b_plus_tree_insert_test.cpp > /tmp/checksums/test2_b_plus_tree_insert.sha256
sha256sum test/storage/b_plus_tree_sequential_scale_test.cpp > /tmp/checksums/test2_b_plus_tree_sequential_scale.sha256
sha256sum test/storage/b_plus_tree_delete_test.cpp > /tmp/checksums/test2_b_plus_tree_delete.sha256
sha256sum test/storage/b_plus_tree_concurrent_test.cpp > /tmp/checksums/test2_b_plus_tree_concurrent.sha256
# Task 3 test files
sha256sum test/sql/p3.00-primer.slt > /tmp/checksums/test3_primer.sha256
# Task 4 test files
sha256sum test/concurrency/txn_timestamp_test.cpp > /tmp/checksums/test4_txn_timestamp.sha256
sha256sum test/concurrency/txn_scan_test.cpp > /tmp/checksums/test4_txn_scan.sha256
sha256sum test/concurrency/txn_executor_test.cpp > /tmp/checksums/test4_txn_executor.sha256

echo "Building project"
mkdir -p build && cd build
cmake -DCMAKE_BUILD_TYPE=Debug .. > /dev/null 2>&1
make -j$(nproc) > /dev/null 2>&1

echo "Setup complete"

