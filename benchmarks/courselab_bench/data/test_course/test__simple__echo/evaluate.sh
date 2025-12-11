#!/bin/bash
set -e

echo "=== Evaluation ==="

if [ ! -f result.txt ]; then
    echo "FAIL: result.txt does not exist"
    exit 1
fi

content=$(cat result.txt)
if [ "$content" = "SUCCESS" ]; then
    echo "PASS: result.txt contains 'SUCCESS'"
    exit 0
else
    echo "FAIL: result.txt does not contain 'SUCCESS' (found: '$content')"
    exit 1
fi
