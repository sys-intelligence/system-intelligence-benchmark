#!/bin/bash

#----------------------------------------------#
# Scoring Scheme:                              #
# 0%: build pass                              #
# 80%: test pass                               #
# 20%: code format pass                        #
#----------------------------------------------#

set -e

echo "=== Evaluating CountMinSketch Task ==="

cd /workspace

echo "Verifying protected files were not modified"
PROTECTED_FILES=(
    "test/primer/count_min_sketch_test.cpp:count_min_sketch_test.cpp.sha256"
)

for entry in "${PROTECTED_FILES[@]}"; do
    file="${entry%%:*}"
    checksum_name="${entry##*:}"
    if [ -f "$file" ] && [ -f "/tmp/checksums/${checksum_name}" ]; then
        if ! sha256sum -c "/tmp/checksums/${checksum_name}" > /dev/null 2>&1; then
            echo "FAIL: $file was modified"
            exit 1
        fi
    fi
done
echo "All protected files unchanged"

# Initialize scores
BUILD_SCORE=0
TEST_SCORE=0
FORMAT_SCORE=0

# Step 1: Build
echo "=== Step 1: Build ==="

# Remove existing build directory
if [ -d "build" ]; then
    echo "Removing existing build directory"
    rm -rf build
fi

# Create build directory and build
echo "Creating build directory and building..."
if mkdir build && cd build && cmake -DCMAKE_BUILD_TYPE=Debug .. && make -j$(nproc); then
    echo "Build successful"
    BUILD_SCORE=0  # Build is a prerequisite, not scored
    cd /workspace
else
    echo "FAIL: Build failed"
    cd /workspace
    exit 1
fi

# Step 2: Correctness Test (80% of total score)
echo ""
echo "=== Step 2: Correctness Test (80% of score) ==="

cd build

# Build the test target
echo "Building count_min_sketch_test..."
if ! make -j$(nproc) count_min_sketch_test > test_build_output.txt 2>&1; then
    echo "FAIL: Failed to build count_min_sketch_test"
    cat test_build_output.txt
    cd /workspace
    exit 1
fi

# Run the test (capture output even if tests fail)
echo "Running count_min_sketch_test..."
./test/count_min_sketch_test > test_output.txt 2>&1 || true
test_output=$(cat test_output.txt)
echo "$test_output"

# Parse test results from Google Test output
# Look for patterns like:
# [  PASSED  ] X tests.
# [  FAILED  ] Y tests, listed below:
# [----------] Z tests from TestSuiteName

passed_tests=0
failed_tests=0
total_tests=0

# Extract passed tests count from summary line like "[  PASSED  ] 0 tests."
if echo "$test_output" | grep -qE "\[  PASSED  \].*tests"; then
    passed_line=$(echo "$test_output" | grep -E "\[  PASSED  \].*tests" | head -1)
    passed_tests=$(echo "$passed_line" | grep -oE "[0-9]+" | head -1)
    passed_tests=${passed_tests:-0}
fi

# Extract failed tests count from summary line like "[  FAILED  ] 13 tests, listed below:"
if echo "$test_output" | grep -qE "\[  FAILED  \].*tests"; then
    failed_line=$(echo "$test_output" | grep -E "\[  FAILED  \].*tests" | head -1)
    failed_tests=$(echo "$failed_line" | grep -oE "[0-9]+" | head -1)
    failed_tests=${failed_tests:-0}
fi

# Extract total tests from test suite summary like "[----------] 13 tests from CountMinSketchTest"
if echo "$test_output" | grep -qE "\[----------\].*tests from"; then
    suite_line=$(echo "$test_output" | grep -E "\[----------\].*tests from" | tail -1)
    total_tests=$(echo "$suite_line" | grep -oE "[0-9]+" | head -1)
    total_tests=${total_tests:-0}
fi

# If total_tests is still 0, calculate from passed + failed
if [ "$total_tests" -eq 0 ] && [ $((passed_tests + failed_tests)) -gt 0 ]; then
    total_tests=$((passed_tests + failed_tests))
fi

# If still no tests found, try to count individual test cases from detailed output
if [ "$total_tests" -eq 0 ]; then
    # Count test cases from output like "[  FAILED  ] CountMinSketchTest.BasicTest1"
    total_tests=$(echo "$test_output" | grep -cE "\[  (PASSED|FAILED)  \].*\." || echo "0")
    passed_tests=$(echo "$test_output" | grep -cE "\[  PASSED  \].*\." || echo "0")
    failed_tests=$(echo "$test_output" | grep -cE "\[  FAILED  \].*\." || echo "0")
fi

echo "Test Results:"
echo "  Total tests: $total_tests"
echo "  Passed: $passed_tests"
echo "  Failed: $failed_tests"

if [ "$total_tests" -gt 0 ]; then
    # Calculate test score (80% of total)
    # Use awk for floating point calculation if bc is not available
    if command -v bc >/dev/null 2>&1; then
        test_percentage=$(echo "scale=2; $passed_tests * 100 / $total_tests" | bc)
        TEST_SCORE=$(echo "scale=2; $passed_tests * 0.8 / $total_tests" | bc)
    else
        test_percentage=$(awk "BEGIN {printf \"%.2f\", $passed_tests * 100 / $total_tests}")
        TEST_SCORE=$(awk "BEGIN {printf \"%.2f\", $passed_tests * 0.8 / $total_tests}")
    fi
    echo "  Test score: $TEST_SCORE / 0.80 (${test_percentage}% of tests passed)"
else
    echo "WARNING: Could not determine test count from output"
    TEST_SCORE=0
fi

# Already in build directory from step 2

# Step 3: Format Check (20% of total score)
echo ""
echo "=== Step 3: Format Check (20% of score) ==="

# Run format
echo "Running make format..."
if make format > format_output.txt 2>&1; then
    echo "Format applied successfully"
else
    echo "WARNING: make format had issues"
    cat format_output.txt
fi

# Check clang-tidy
echo "Running make check-clang-tidy-p0..."
if make check-clang-tidy-p0 > clang_tidy_output.txt 2>&1; then
    echo "clang-tidy check passed"
    FORMAT_SCORE=0.20
else
    echo "FAIL: clang-tidy check failed"
    cat clang_tidy_output.txt
    FORMAT_SCORE=0
fi

# Calculate and display final score
echo ""
echo "=== Final Score ==="
if command -v bc >/dev/null 2>&1; then
    TOTAL_SCORE=$(echo "scale=2; $BUILD_SCORE + $TEST_SCORE + $FORMAT_SCORE" | bc)
else
    TOTAL_SCORE=$(awk "BEGIN {printf \"%.2f\", $BUILD_SCORE + $TEST_SCORE + $FORMAT_SCORE}")
fi
echo "Build: $BUILD_SCORE / 0.00 (prerequisite)"
echo "Test: $TEST_SCORE / 0.80"
echo "Format: $FORMAT_SCORE / 0.20"
echo "Total: $TOTAL_SCORE / 1.00"

# Check if total score is 1.00 or higher
if command -v bc >/dev/null 2>&1; then
    if (( $(echo "$TOTAL_SCORE >= 1.00" | bc -l) )); then
        echo "PASS: All checks passed"
        exit 0
    else
        echo "FAIL: Some checks failed"
        exit 1
    fi
else
    # Use awk for comparison if bc is not available
    if awk "BEGIN {exit !($TOTAL_SCORE >= 1.00)}"; then
        echo "PASS: All checks passed"
        exit 0
    else
        echo "FAIL: Some checks failed"
        exit 1
    fi
fi
