#!/bin/bash
set -e

echo "=== Evaluation ==="

cd /workspace/processes-shell

if [ -f /tmp/checksums/protected.sha256 ]; then
  sha256sum -c /tmp/checksums/protected.sha256 || {
    echo "FAIL: protected files were modified"
    exit 1
  }
fi

echo "Building wish"
if [ -f Makefile ]; then
  make
else
  gcc -D_GNU_SOURCE -std=gnu11 -Wall -Werror -O2 -o wish *.c
fi

echo "Running tests"
bash test-wish.sh
