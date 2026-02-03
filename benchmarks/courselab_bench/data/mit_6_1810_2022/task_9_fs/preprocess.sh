#!/bin/bash
set -e


cd /root

# Clone MIT xv6-labs-2022 skeleton (fs branch)
git clone git://g.csail.mit.edu/xv6-labs-2022 workspace
cd workspace
git checkout fs
# Pin to specific commit for reproducibility
git checkout 888b75593bd6b4c387d2dcf3e492c430145b9734
rm -rf .git

# Create checksums for protected files (grading scripts, tests)
mkdir -p /tmp/checksums
sha256sum grade-lab-fs > /tmp/checksums/grade-lab-fs.sha256
sha256sum gradelib.py > /tmp/checksums/gradelib.py.sha256
sha256sum user/bigfile.c > /tmp/checksums/user_bigfile.c.sha256
sha256sum user/symlinktest.c > /tmp/checksums/user_symlinktest.c.sha256
