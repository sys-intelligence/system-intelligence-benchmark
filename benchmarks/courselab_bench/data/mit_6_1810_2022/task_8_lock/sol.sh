#!/bin/bash
# Reference solution from: https://github.com/Cyrus-iwnl/xv6-labs-2022
set -e

# Clone reference solution repository
git clone https://github.com/Cyrus-iwnl/xv6-labs-2022.git /tmp/ref
cd /tmp/ref
git checkout origin/lock

# Copy solution files
cp kernel/bio.c /root/workspace/kernel/
cp kernel/kalloc.c /root/workspace/kernel/

cd /root/workspace

# Create time.txt (required by grading script - contains hours spent)
echo "1" > time.txt

# Clean up
rm -rf /tmp/ref
