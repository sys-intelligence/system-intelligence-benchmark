#!/bin/bash
set -euo pipefail

echo "=== Evaluating Attack Lab ==="
cd /workspace

echo "Verifying protected files"
if [ -f /tmp/checksums/protected.sha256 ]; then
    sha256sum -c /tmp/checksums/protected.sha256
else
    echo "WARN: No protected checksums found; continuing"
fi

echo "Checking required binaries"
for bin in ctarget rtarget hex2raw; do
    if [ ! -x "$bin" ]; then
        echo "FAIL: $bin is missing or not executable"
        exit 1
    fi
done

echo "Checking solution files"
solutions=(phase1.txt phase2.txt phase3.txt phase4.txt phase5.txt)
for sol in "${solutions[@]}"; do
    if [ ! -f "$sol" ]; then
        echo "FAIL: Missing solution file $sol"
        exit 1
    fi
    if [ ! -s "$sol" ]; then
        echo "FAIL: Solution file $sol is empty"
        exit 1
    fi
done

run_phase() {
    local phase_id="$1"
    local target_bin="$2"
    local hex_file="$3"
    local expect_pattern="$4"

    echo "--- Phase ${phase_id} (${target_bin}) ---"
    local raw_file="/tmp/raw_phase_${phase_id}.bin"

    if ! ./hex2raw < "$hex_file" > "$raw_file"; then
        echo "FAIL: hex2raw failed for $hex_file"
        exit 1
    fi

    local output
    local status=0
    output=$(timeout 30 "./${target_bin}" -q -i "$raw_file" 2>&1) || status=$?
    echo "$output"

    if [ "$status" -ne 0 ]; then
        echo "FAIL: ${target_bin} exited with status $status for phase ${phase_id}"
        exit 1
    fi

    if echo "$output" | grep -qi "Misfire"; then
        echo "FAIL: ${target_bin} reported a misfire for phase ${phase_id}"
        exit 1
    fi

    if ! echo "$output" | grep -q "$expect_pattern"; then
        echo "FAIL: Expected success pattern '$expect_pattern' not found for phase ${phase_id}"
        exit 1
    fi

    echo "Phase ${phase_id} passed"
}

run_phase 1 ctarget phase1.txt "Touch1!: You called touch1()"
run_phase 2 ctarget phase2.txt "Touch2!: You called touch2(0x"
run_phase 3 ctarget phase3.txt "Touch3!: You called touch3(\""
run_phase 4 rtarget phase4.txt "Touch2!: You called touch2(0x"
run_phase 5 rtarget phase5.txt "Touch3!: You called touch3(\""

echo "PASS: All attack lab phases completed"
exit 0
