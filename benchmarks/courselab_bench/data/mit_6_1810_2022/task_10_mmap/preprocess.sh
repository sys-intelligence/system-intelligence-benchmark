#!/bin/bash
set -e


cd /root

# Clone MIT xv6-labs-2022 skeleton (mmap branch)
git clone git://g.csail.mit.edu/xv6-labs-2022 workspace
cd workspace
git checkout mmap
# Pin to specific commit for reproducibility
git checkout 9cc6b8345397c1f06cc93ed3fbaa20709cb1984e
rm -rf .git

# Create checksums for protected files (grading scripts, tests)
mkdir -p /tmp/checksums
sha256sum grade-lab-mmap > /tmp/checksums/grade-lab-mmap.sha256
sha256sum gradelib.py > /tmp/checksums/gradelib.py.sha256
sha256sum user/mmaptest.c > /tmp/checksums/user_mmaptest.c.sha256
