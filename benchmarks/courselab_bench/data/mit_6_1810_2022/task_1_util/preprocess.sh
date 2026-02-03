#!/bin/bash
set -e


cd /root

# Clone MIT xv6-labs-2022 skeleton (util branch)
git clone git://g.csail.mit.edu/xv6-labs-2022 workspace
cd workspace
git checkout util
# Pin to specific commit for reproducibility
git checkout dc9153fcb9c9b762dfaae9f586aecdaf04fb68fe
rm -rf .git

# Create checksums for protected files (grading scripts, tests)
mkdir -p /tmp/checksums
sha256sum grade-lab-util > /tmp/checksums/grade-lab-util.sha256
sha256sum gradelib.py > /tmp/checksums/gradelib.py.sha256
sha256sum user/xargstest.sh > /tmp/checksums/user_xargstest.sh.sha256
