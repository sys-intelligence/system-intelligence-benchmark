#!/bin/bash
set -e


cd /root

# Clone MIT xv6-labs-2022 skeleton (traps branch)
git clone git://g.csail.mit.edu/xv6-labs-2022 workspace
cd workspace
git checkout traps
# Pin to specific commit for reproducibility
git checkout c826bd8176c764a7ae385ba6567afc0cd91cfc69
rm -rf .git

# Create checksums for protected files (grading scripts, tests)
mkdir -p /tmp/checksums
sha256sum grade-lab-traps > /tmp/checksums/grade-lab-traps.sha256
sha256sum gradelib.py > /tmp/checksums/gradelib.py.sha256
sha256sum user/alarmtest.c > /tmp/checksums/user_alarmtest.c.sha256
