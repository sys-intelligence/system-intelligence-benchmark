#!/bin/bash
set -e

cd /home/PKUOS
export PATH="/home/PKUOS/toolchain/x86_64/bin:$PATH"

git clone https://github.com/PKU-OS/pintos.git pintos
cd pintos
rm -rf .git

echo 'export PATH="/home/PKUOS/pintos/src/utils:/home/PKUOS/toolchain/x86_64/bin:$PATH"' >> /home/PKUOS/.bashrc

mkdir -p /tmp/checksums
for file in src/tests/userprog/*.c src/tests/userprog/*.ck src/tests/userprog/no-vm/*.c src/tests/userprog/no-vm/*.ck; do
    [ -f "$file" ] && sha256sum "$file" > "/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
done
sha256sum src/userprog/Make.vars > /tmp/checksums/src_userprog_Make.vars.sha256
sha256sum src/tests/Make.tests > /tmp/checksums/src_tests_Make.tests.sha256
