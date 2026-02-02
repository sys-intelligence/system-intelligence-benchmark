#!/bin/bash
set -euo pipefail

echo "=== Evaluating Cache Lab ==="
cd /workspace

if [ -f /tmp/checksums/protected.sha256 ]; then
    echo "Verifying protected files"
    sha256sum -c /tmp/checksums/protected.sha256
else
    echo "WARN: No protected checksums found; continuing"
fi

required=(
  "csim.c"
  "trans.c"
  "cachelab.c"
  "cachelab.h"
  "test-csim"
  "test-trans.c"
  "tracegen.c"
  "Makefile"
  "traces/yi.trace"
  "traces/yi2.trace"
  "traces/dave.trace"
  "traces/trans.trace"
  "traces/long.trace"
)
for f in "${required[@]}"; do
    if [ ! -e "$f" ]; then
        echo "FAIL: Missing required file $f"
        exit 1
    fi
done

echo "Building"
make clean >/dev/null 2>&1 || true
if ! timeout 300 make >/tmp/cachelab_build.log 2>&1; then
    echo "FAIL: make failed"
    tail -n 50 /tmp/cachelab_build.log
    exit 1
fi

chmod +x test-csim test-trans csim-ref driver.py || true

echo "Running test-csim"
csim_output=$(timeout 300 ./test-csim 2>&1) || {
    echo "FAIL: test-csim failed to run"
    echo "$csim_output"
    exit 1
}
echo "$csim_output"
csim_result=$(echo "$csim_output" | grep "TEST_CSIM_RESULTS" | tail -n1 | awk -F '=' '{print $2}')
if ! echo "$csim_result" | grep -Eq "^[0-9]+$"; then
    echo "FAIL: Could not parse TEST_CSIM_RESULTS (got '$csim_result')"
    exit 1
fi

expected_csim=27
if [ "$csim_result" -ne "$expected_csim" ]; then
    echo "FAIL: Cache simulator score unexpected (got $csim_result, expected $expected_csim)"
    exit 1
fi

run_trans_test() {
    local M="$1"
    local N="$2"
    local label="$3"

    echo "Running test-trans for $label (${M}x${N})"
    local output
    local status=0
    output=$(timeout 300 ./test-trans -M "$M" -N "$N" 2>&1) || status=$?
    echo "$output"
    if [ "$status" -ne 0 ]; then
        echo "FAIL: test-trans exited with status $status for $label"
        exit 1
    fi

    local line
    line=$(echo "$output" | grep "TEST_TRANS_RESULTS" | tail -n1 | awk -F '=' '{print $2}')
    if [ -z "$line" ]; then
        echo "FAIL: Could not parse TEST_TRANS_RESULTS for $label"
        exit 1
    fi

    local correct="${line%%:*}"
    local misses="${line##*:}"

    if [ "$correct" != "1" ]; then
        echo "FAIL: Transpose failed correctness for $label"
        exit 1
    fi

    if [ "$misses" = "2147483647" ] || ! echo "$misses" | grep -Eq "^[0-9]+$"; then
        echo "FAIL: Invalid miss count for $label ($misses)"
        exit 1
    fi

    # Enforce performance budgets similar to the autograder scoring windows
    local budget=0
    case "$label" in
        "32x32") budget=600 ;;
        "64x64") budget=2000 ;;
        "61x67") budget=3000 ;;
    esac

    if [ "$budget" -gt 0 ]; then
        awk "BEGIN { if ($misses > $budget) exit 1; }" || {
            echo "FAIL: Miss count $misses exceeds budget $budget for $label"
            exit 1
        }
    fi
}

run_trans_test 32 32 "32x32"
run_trans_test 64 64 "64x64"
run_trans_test 61 67 "61x67"

echo "PASS: Cache lab simulator and transpose verified"
exit 0