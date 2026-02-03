#!/bin/bash
set -e


cd /root

# Clone MIT xv6-labs-2022 skeleton (lock branch)
git clone git://g.csail.mit.edu/xv6-labs-2022 workspace
cd workspace
git checkout lock
# Pin to specific commit for reproducibility
git checkout ad57ec8cb93867b5ec81a39e35e7cf08c64cf775
rm -rf .git

# Create checksums for protected files (grading scripts, tests)
mkdir -p /tmp/checksums
sha256sum grade-lab-lock > /tmp/checksums/grade-lab-lock.sha256
sha256sum gradelib.py > /tmp/checksums/gradelib.py.sha256
sha256sum user/kalloctest.c > /tmp/checksums/user_kalloctest.c.sha256
sha256sum user/bcachetest.c > /tmp/checksums/user_bcachetest.c.sha256
