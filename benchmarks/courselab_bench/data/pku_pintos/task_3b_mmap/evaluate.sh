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

# Lab 3b specific VM tests (24 tests)
# Stack growth tests (6)
LAB3B_STACK_TESTS="page-merge-mm page-merge-stk pt-grow-stack pt-grow-stk-sc pt-big-stk-obj pt-grow-pusha"
# Mmap tests (18)
LAB3B_MMAP_TESTS="mmap-read mmap-write mmap-shuffle mmap-twice mmap-unmap mmap-exit mmap-clean mmap-close mmap-remove mmap-bad-fd mmap-inherit mmap-null mmap-zero mmap-misalign mmap-over-code mmap-over-data mmap-over-stk mmap-overlap"

# Count results for Lab 3b tests only
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

# Count Lab 3b stack growth tests
stack_passed=0
stack_failed=0
for test in $LAB3B_STACK_TESTS; do
    if grep -q "^pass tests/vm/$test" /tmp/test_output.txt; then
        passed=$((passed + 1))
        stack_passed=$((stack_passed + 1))
    elif grep -q "^FAIL tests/vm/$test" /tmp/test_output.txt; then
        failed=$((failed + 1))
        stack_failed=$((stack_failed + 1))
    fi
done

# Count Lab 3b mmap tests
mmap_passed=0
mmap_failed=0
for test in $LAB3B_MMAP_TESTS; do
    if grep -q "^pass tests/vm/$test" /tmp/test_output.txt; then
        passed=$((passed + 1))
        mmap_passed=$((mmap_passed + 1))
    elif grep -q "^FAIL tests/vm/$test" /tmp/test_output.txt; then
        failed=$((failed + 1))
        mmap_failed=$((mmap_failed + 1))
    fi
done

total=$((passed + failed))
echo ""
echo "=== Lab 3b Results ==="
echo "Userprog: $userprog_passed passed, $userprog_failed failed"
echo "Filesys/base: $filesys_passed passed, $filesys_failed failed"
echo "Stack growth (Lab 3b): $stack_passed of 6 passed"
echo "Mmap (Lab 3b): $mmap_passed of 18 passed"
echo "Total: $passed/$total tests passed"

if [ $failed -eq 0 ] && [ $total -gt 0 ]; then
    echo "All Lab 3b tests passed!"
    exit 0
fi

if [ $passed -gt 0 ]; then
    echo "Partial: $passed/$total tests passed"
    exit 0
fi

echo "FAIL: Tests did not pass"
exit 1
