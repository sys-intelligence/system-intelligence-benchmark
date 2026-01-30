#!/bin/bash
set -e

cd /home/PKUOS
export PATH="/home/PKUOS/toolchain/x86_64/bin:$PATH"

git clone https://github.com/PKU-OS/pintos.git pintos
cd pintos
rm -rf .git

echo 'export PATH="/home/PKUOS/pintos/src/utils:/home/PKUOS/toolchain/x86_64/bin:$PATH"' >> /home/PKUOS/.bashrc

# Create checksums for protected files (tests and build config)
mkdir -p /tmp/checksums

# Userprog tests (Lab 2 tests must still pass)
for file in src/tests/userprog/*.c src/tests/userprog/*.ck src/tests/userprog/no-vm/*.c src/tests/userprog/no-vm/*.ck; do
    [ -f "$file" ] && sha256sum "$file" > "/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
done

# VM tests
for file in src/tests/vm/*.c src/tests/vm/*.ck; do
    [ -f "$file" ] && sha256sum "$file" > "/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
done

# Filesys base tests
for file in src/tests/filesys/base/*.c src/tests/filesys/base/*.ck; do
    [ -f "$file" ] && sha256sum "$file" > "/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
done

# Build configuration files
sha256sum src/vm/Make.vars > /tmp/checksums/src_vm_Make.vars.sha256
sha256sum src/tests/Make.tests > /tmp/checksums/src_tests_Make.tests.sha256

echo "PKU Pintos Lab 3b (Mmap Files) environment ready"
