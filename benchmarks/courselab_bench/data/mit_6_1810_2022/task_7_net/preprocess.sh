#!/bin/bash
set -e

cd /root

# Clone skeleton repository
git clone git://g.csail.mit.edu/xv6-labs-2022 workspace
cd workspace
git checkout net
# Pin to specific commit for reproducibility
git checkout 71061515337fe191b3ed0802e132d7b0fd8d08ef
rm -rf .git

# Create checksums for protected files (grading scripts, tests)
mkdir -p /tmp/checksums
sha256sum grade-lab-net > /tmp/checksums/grade-lab-net.sha256
sha256sum gradelib.py > /tmp/checksums/gradelib.py.sha256
sha256sum user/nettests.c > /tmp/checksums/user_nettests.c.sha256
