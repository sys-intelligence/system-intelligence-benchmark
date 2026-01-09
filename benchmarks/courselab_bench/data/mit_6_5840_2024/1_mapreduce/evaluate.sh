#!/bin/bash
set -e

echo "=== Evaluation ==="

cd /workspace

export PATH=$PATH:/usr/local/go/bin

echo "Verifying protected files were not modified"
PROTECTED_FILES=(
    "src/main/mrcoordinator.go"
    "src/main/mrworker.go"
    "src/main/mrsequential.go"
    "src/main/test-mr.sh"
)

for file in "${PROTECTED_FILES[@]}"; do
    if [ -f "$file" ] && [ -f "/tmp/checksums/$(basename $file).sha256" ]; then
        echo "  Checking $file"
        sha256sum -c "/tmp/checksums/$(basename $file).sha256" || {
            echo "FAIL: $file was modified"
            exit 1
        }
    fi
done
echo "All protected files unchanged"

echo "Running MapReduce tests"
cd src/main
timeout 600 bash test-mr.sh 2>&1 | tee test_output.txt

echo "Checking test results"
if grep -q 'PASSED ALL TESTS' test_output.txt; then
    echo "PASS: All tests passed"
    exit 0
else
    echo "FAIL: Tests did not pass"
    exit 1
fi
