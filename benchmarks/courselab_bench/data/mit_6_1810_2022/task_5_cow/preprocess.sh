#!/bin/bash
set -e


cd /root

# Clone MIT xv6-labs-2022 skeleton (cow branch)
git clone git://g.csail.mit.edu/xv6-labs-2022 workspace
cd workspace
git checkout cow
# Pin to specific commit for reproducibility
git checkout a4ef3e1a5ae48457e228e343127e73d8fa2388ac
rm -rf .git

# Create checksums for protected files (grading scripts, tests)
mkdir -p /tmp/checksums
sha256sum grade-lab-cow > /tmp/checksums/grade-lab-cow.sha256
sha256sum gradelib.py > /tmp/checksums/gradelib.py.sha256
sha256sum user/cowtest.c > /tmp/checksums/user_cowtest.c.sha256
