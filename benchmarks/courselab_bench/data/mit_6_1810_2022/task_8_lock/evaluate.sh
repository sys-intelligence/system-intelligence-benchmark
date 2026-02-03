#!/bin/bash
set -e

cd /root/workspace

# Verify protected files unchanged
for file in grade-lab-lock gradelib.py user/kalloctest.c user/bcachetest.c; do
    checksum="/tmp/checksums/$(echo "$file" | tr '/' '_').sha256"
    if [ -f "$checksum" ]; then
        sha256sum -c "$checksum" > /dev/null 2>&1 || { echo "FAIL: $file modified"; exit 1; }
    fi
done

# Run grading with retries (tests can be timing-sensitive)
for attempt in 1 2 3; do
    if make LAB=lock grade 2>&1 | tee /tmp/grade_output.txt | grep -q "Score:.*80/80"; then
        echo "PASS: All tests passed"
        exit 0
    fi
    [ $attempt -lt 3 ] && sleep 2
done

echo "FAIL: Tests did not pass"
cat /tmp/grade_output.txt
exit 1
