#!/bin/bash
set -e

export PATH="/home/PKUOS/pintos/src/utils:/home/PKUOS/toolchain/x86_64/bin:$PATH"
cd /home/PKUOS/pintos

# Verify protected files unchanged
for file in src/tests/userprog/*.c src/tests/userprog/*.ck src/tests/userprog/no-vm/*.c src/tests/userprog/no-vm/*.ck; do
    [ -f "$file" ] || continue
    checksum="/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
    [ -f "$checksum" ] && sha256sum -c "$checksum" > /dev/null 2>&1 || { echo "FAIL: $file modified"; exit 1; }
done
for file in src/tests/vm/*.c src/tests/vm/*.ck; do
    [ -f "$file" ] || continue
    checksum="/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
    [ -f "$checksum" ] && sha256sum -c "$checksum" > /dev/null 2>&1 || { echo "FAIL: $file modified"; exit 1; }
done
for file in src/tests/filesys/base/*.c src/tests/filesys/base/*.ck; do
    [ -f "$file" ] || continue
    checksum="/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
    [ -f "$checksum" ] && sha256sum -c "$checksum" > /dev/null 2>&1 || { echo "FAIL: $file modified"; exit 1; }
done
for file in src/vm/Make.vars src/tests/Make.tests; do
    checksum="/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
    [ -f "$checksum" ] && sha256sum -c "$checksum" > /dev/null 2>&1 || { echo "FAIL: $file modified"; exit 1; }
done

cd src/vm
make clean 2>/dev/null || true
make

cd build
make check 2>&1 | tee /tmp/test_output.txt

# Lab 3a specific VM tests (10 tests)
LAB3A_VM_TESTS="page-linear page-parallel page-shuffle page-merge-seq page-merge-par pt-bad-addr pt-bad-read pt-write-code pt-write-code2 pt-grow-bad"

# Count results for Lab 3a tests only
passed=0
failed=0

# Count userprog tests (all should pass)
userprog_passed=$(grep -E "^pass tests/userprog/" /tmp/test_output.txt | wc -l)
userprog_failed=$(grep -E "^FAIL tests/userprog/" /tmp/test_output.txt | wc -l)
passed=$((passed + userprog_passed))
failed=$((failed + userprog_failed))

# Count filesys/base tests (all should pass)
filesys_passed=$(grep -E "^pass tests/filesys/base/" /tmp/test_output.txt | wc -l)
filesys_failed=$(grep -E "^FAIL tests/filesys/base/" /tmp/test_output.txt | wc -l)
passed=$((passed + filesys_passed))
failed=$((failed + filesys_failed))

# Count only the 10 specific Lab 3a VM tests
for test in $LAB3A_VM_TESTS; do
    if grep -q "^pass tests/vm/$test" /tmp/test_output.txt; then
        passed=$((passed + 1))
    elif grep -q "^FAIL tests/vm/$test" /tmp/test_output.txt; then
        failed=$((failed + 1))
    fi
done

total=$((passed + failed))
echo ""
echo "=== Lab 3a Results ==="
echo "Userprog: $userprog_passed passed, $userprog_failed failed"
echo "Filesys/base: $filesys_passed passed, $filesys_failed failed"
echo "VM (Lab 3a specific): $((passed - userprog_passed - filesys_passed)) of 10 passed"
echo "Total: $passed/$total tests passed"

if [ $failed -eq 0 ] && [ $total -gt 0 ]; then
    echo "All Lab 3a tests passed!"
    exit 0
fi

if [ $passed -gt 0 ]; then
    echo "Partial: $passed/$total tests passed"
    exit 0
fi

echo "FAIL: Tests did not pass"
exit 1
