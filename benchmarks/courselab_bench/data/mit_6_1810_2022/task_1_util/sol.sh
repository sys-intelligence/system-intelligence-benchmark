#!/bin/bash
# Reference solution from: https://github.com/Cyrus-iwnl/xv6-labs-2022
set -e

# Clone reference solution repository
git clone https://github.com/Cyrus-iwnl/xv6-labs-2022.git /tmp/ref
cd /tmp/ref
git checkout ca425c7b43e5c4a805cbfaaebfb6556a9ff9e7cb

# Copy solution files
cp user/sleep.c /root/workspace/user/
cp user/pingpong.c /root/workspace/user/
cp user/primes.c /root/workspace/user/
cp user/find.c /root/workspace/user/
cp user/xargs.c /root/workspace/user/

# Update Makefile to add new programs to UPROGS
# Add the new programs after _zombie in the UPROGS list
cd /root/workspace
sed -i 's|\$U/_zombie\\|\$U/_zombie\\\n\t\$U/_sleep\\\n\t\$U/_pingpong\\\n\t\$U/_primes\\\n\t\$U/_find\\\n\t\$U/_xargs\\|' Makefile

# Create time.txt (required by grading script - contains hours spent)
echo "1" > time.txt

# Clean up
rm -rf /tmp/ref
