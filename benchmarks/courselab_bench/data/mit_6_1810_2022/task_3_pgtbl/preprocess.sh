#!/bin/bash
set -e


cd /root

# Clone MIT xv6-labs-2022 skeleton (pgtbl branch)
git clone git://g.csail.mit.edu/xv6-labs-2022 workspace
cd workspace
git checkout pgtbl
# Pin to specific commit for reproducibility
git checkout b1083ee059a2aa0e018676f4f3790cb3bafaa1c5
rm -rf .git

# Create checksums for protected files (grading scripts, tests)
mkdir -p /tmp/checksums
sha256sum grade-lab-pgtbl > /tmp/checksums/grade-lab-pgtbl.sha256
sha256sum gradelib.py > /tmp/checksums/gradelib.py.sha256
sha256sum user/pgtbltest.c > /tmp/checksums/user_pgtbltest.c.sha256
