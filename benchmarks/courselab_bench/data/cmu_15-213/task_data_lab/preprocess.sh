#!/bin/bash
set -e

echo "=== Setting up CMU 15-213 Data Lab ==="

cd /workspace

echo "Making dlc executable"
chmod +x dlc

echo "Installing build dependencies"
apt-get update > /dev/null 2>&1
apt-get install -y build-essential gcc-multilib make perl libc6-dev-i386 > /dev/null 2>&1

echo "Cleaning any existing build artifacts"
make clean > /dev/null 2>&1 || true

echo "Verifying all required files are present"
required_files="bits.c bits.h btest.c btest.h decl.c tests.c dlc Makefile"
for file in $required_files; do
    if [ ! -f "$file" ]; then
        echo "ERROR: Required file $file is missing"
        exit 1
    fi
    echo "  ✓ $file"
done

echo "Creating checksums for protected files"
protected_files="btest.c btest.h decl.c tests.c dlc driver.pl Driverhdrs.pm Driverlib.pm fshow.c ishow.c Makefile README"

mkdir -p /tmp/checksums
CHECKSUM_FILE=/tmp/checksums/protected.sha256
: > "$CHECKSUM_FILE"

for file in $protected_files; do
    if [ -f "$file" ]; then
        sha256sum "$file" >> "$CHECKSUM_FILE"
        echo "  Protected: $file"
    fi
done

echo "Setup complete"
exit 0
