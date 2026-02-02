#!/bin/bash
set -euo pipefail

echo "=== Evaluating Buffer Lab ==="
cd /workspace

USER_ID="agent007"

if [ -f /tmp/checksums/protected.sha256 ]; then
    echo "Verifying protected files"
    sha256sum -c /tmp/checksums/protected.sha256
else
    echo "WARN: No protected checksums found; continuing"
fi

echo "Checking required binaries"
for bin in bufbomb hex2raw makecookie; do
    if [ ! -x "$bin" ]; then
        echo "FAIL: $bin is missing or not executable"
        exit 1
    fi
done

echo "Checking solution files"
solutions=(smoke.txt fizz.txt bang.txt boom.txt kaboom.txt)
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

cookie=""
if output=$(./makecookie "$USER_ID" 2>/dev/null); then
    cookie="$output"
    echo "Computed cookie for $USER_ID: $cookie"
else
    echo "WARN: makecookie failed; continuing"
fi

run_phase() {
    local phase_name="$1"
    local hex_file="$2"
    local expect_pattern="$3"

    echo "--- Phase ${phase_name} ---"
    local raw_file="/tmp/raw_${phase_name}.bin"

    if ! ./hex2raw < "$hex_file" > "$raw_file"; then
        echo "FAIL: hex2raw failed for $hex_file"
        exit 1
    fi

    local output
    local status=0
    output=$(cat "$raw_file" | timeout 30 ./bufbomb -u "$USER_ID" 2>&1) || status=$?
    echo "$output"

    if [ "$status" -ne 0 ]; then
        echo "FAIL: bufbomb exited with status $status for phase ${phase_name}"
        exit 1
    fi

    if echo "$output" | grep -qi "Misfire"; then
        echo "FAIL: bufbomb reported a misfire for phase ${phase_name}"
        exit 1
    fi

    if ! echo "$output" | grep -q "$expect_pattern"; then
        echo "FAIL: Expected success pattern '$expect_pattern' not found for phase ${phase_name}"
        exit 1
    fi

    echo "Phase ${phase_name} passed"
}

run_phase smoke smoke.txt "Smoke!: You called smoke()"
run_phase fizz  fizz.txt  "Fizz!: You called fizz(0x"
run_phase bang  bang.txt  "Bang!: You set global_value to 0x"
run_phase boom  boom.txt  "Boom!: getbuf returned 0x"
run_phase kaboom kaboom.txt "KABOOM!: getbufn returned 0x"

echo "PASS: All buffer lab phases completed"
exit 0
