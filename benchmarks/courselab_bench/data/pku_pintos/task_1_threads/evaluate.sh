#!/bin/bash
set -e

export PATH="/home/PKUOS/pintos/src/utils:/home/PKUOS/toolchain/x86_64/bin:$PATH"
cd /home/PKUOS/pintos

# Verify protected files unchanged
for file in src/tests/threads/*.c src/tests/threads/*.ck; do
    [ -f "$file" ] || continue
    checksum="/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
    [ -f "$checksum" ] && sha256sum -c "$checksum" > /dev/null 2>&1 || { echo "FAIL: $file modified"; exit 1; }
done
for file in src/threads/Make.vars src/tests/Make.tests; do
    checksum="/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
    [ -f "$checksum" ] && sha256sum -c "$checksum" > /dev/null 2>&1 || { echo "FAIL: $file modified"; exit 1; }
done

# Build and test
cd src/threads
make clean 2>/dev/null || true
make
cd build

# Run with retries (timing-sensitive tests may be flaky)
for attempt in 1 2 3; do
    if make check 2>&1 | tee /tmp/test_output.txt | grep -q "All [0-9]* tests passed"; then
        exit 0
    fi
    [ $attempt -lt 3 ] && sleep 2
done

echo "FAIL: Tests did not pass"
cat /tmp/test_output.txt
exit 1
