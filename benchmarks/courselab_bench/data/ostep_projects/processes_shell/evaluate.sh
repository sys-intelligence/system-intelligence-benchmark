#!/bin/bash
set -e

#!/bin/bash
set -e

echo "=== Evaluation ==="

cd /workspace/processes-shell

echo "Building wish"
if [ -f Makefile ]; then
  make
else
  gcc -D_GNU_SOURCE -std=gnu11 -Wall -Werror -O2 -o wish *.c
fi

echo "Running tests"
bash test-wish.sh
