#!/bin/bash
# Reference solution from: https://github.com/Cyrus-iwnl/xv6-labs-2022
set -e

# Clone reference solution repository
git clone https://github.com/Cyrus-iwnl/xv6-labs-2022.git /tmp/ref
cd /tmp/ref
git checkout origin/fs

# Copy solution files
cp kernel/fcntl.h /root/workspace/kernel/
cp kernel/file.h /root/workspace/kernel/
cp kernel/fs.c /root/workspace/kernel/
cp kernel/fs.h /root/workspace/kernel/
cp kernel/stat.h /root/workspace/kernel/
cp kernel/syscall.c /root/workspace/kernel/
cp kernel/syscall.h /root/workspace/kernel/
cp kernel/sysfile.c /root/workspace/kernel/
cp user/user.h /root/workspace/user/
cp user/usys.pl /root/workspace/user/
cp Makefile /root/workspace/

cd /root/workspace

# Create time.txt (required by grading script - contains hours spent)
echo "1" > time.txt

# Clean up
rm -rf /tmp/ref
