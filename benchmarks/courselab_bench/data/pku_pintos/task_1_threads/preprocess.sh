#!/bin/bash
set -e

cd /home/PKUOS
export PATH="/home/PKUOS/toolchain/x86_64/bin:$PATH"

# Clone PKU Pintos (Docker image has toolchain but not source)
git clone https://github.com/PKU-OS/pintos.git pintos
cd pintos
rm -rf .git

# Add pintos utilities to PATH for agent session
echo 'export PATH="/home/PKUOS/pintos/src/utils:/home/PKUOS/toolchain/x86_64/bin:$PATH"' >> /home/PKUOS/.bashrc

# Create checksums for protected test files
mkdir -p /tmp/checksums
for file in src/tests/threads/*.c src/tests/threads/*.ck; do
    [ -f "$file" ] && sha256sum "$file" > "/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
done
sha256sum src/threads/Make.vars > /tmp/checksums/src_threads_Make.vars.sha256
sha256sum src/tests/Make.tests > /tmp/checksums/src_tests_Make.tests.sha256
