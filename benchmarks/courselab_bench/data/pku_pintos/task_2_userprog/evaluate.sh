#!/bin/bash
set -e

export PATH="/home/PKUOS/pintos/src/utils:/home/PKUOS/toolchain/x86_64/bin:$PATH"
cd /home/PKUOS/pintos

for file in src/tests/userprog/*.c src/tests/userprog/*.ck src/tests/userprog/no-vm/*.c src/tests/userprog/no-vm/*.ck; do
    [ -f "$file" ] || continue
    checksum="/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
    [ -f "$checksum" ] && sha256sum -c "$checksum" > /dev/null 2>&1 || { echo "FAIL: $file modified"; exit 1; }
done
for file in src/userprog/Make.vars src/tests/Make.tests; do
    checksum="/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
    [ -f "$checksum" ] && sha256sum -c "$checksum" > /dev/null 2>&1 || { echo "FAIL: $file modified"; exit 1; }
done

cd src/userprog
make clean 2>/dev/null || true
make

cd build
make check 2>&1 | tee /tmp/test_output.txt

if grep -q "All [0-9]* tests passed" /tmp/test_output.txt; then
    exit 0
fi

if grep -q "pass" /tmp/test_output.txt; then
    passed=$(grep -c "^pass" /tmp/test_output.txt || echo "0")
    total=$(grep -E "^(pass|FAIL)" /tmp/test_output.txt | wc -l)
    echo "Partial: $passed/$total tests passed"
    exit 0
fi

echo "FAIL: Tests did not pass"
exit 1
