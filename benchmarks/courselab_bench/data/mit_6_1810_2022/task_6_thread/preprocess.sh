#!/bin/bash
set -e


cd /root

# Clone MIT xv6-labs-2022 skeleton (thread branch)
git clone git://g.csail.mit.edu/xv6-labs-2022 workspace
cd workspace
git checkout thread
# Pin to specific commit for reproducibility
git checkout ddee41d96a53d67a4b4225aafb6b675bed9d3e7c
rm -rf .git

# Create checksums for protected files (grading scripts, tests)
mkdir -p /tmp/checksums
sha256sum grade-lab-thread > /tmp/checksums/grade-lab-thread.sha256
sha256sum gradelib.py > /tmp/checksums/gradelib.py.sha256
