#!/bin/bash
set -e


cd /root

# Clone MIT xv6-labs-2022 skeleton (syscall branch)
git clone git://g.csail.mit.edu/xv6-labs-2022 workspace
cd workspace
git checkout syscall
# Pin to specific commit for reproducibility
git checkout dc9c09903358605cef705b48746e202c6c9dd4f6
rm -rf .git

# Create checksums for protected files (grading scripts, tests)
mkdir -p /tmp/checksums
sha256sum grade-lab-syscall > /tmp/checksums/grade-lab-syscall.sha256
sha256sum gradelib.py > /tmp/checksums/gradelib.py.sha256
sha256sum user/trace.c > /tmp/checksums/user_trace.c.sha256
sha256sum user/sysinfotest.c > /tmp/checksums/user_sysinfotest.c.sha256
