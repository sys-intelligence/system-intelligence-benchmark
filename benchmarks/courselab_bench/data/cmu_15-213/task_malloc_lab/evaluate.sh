#!/bin/bash
set -euo pipefail

make clean > /dev/null 2>&1 || true
make > /dev/null 2>&1

./mdriver -V -f short1-bal.rep
./mdriver -V -f short2-bal.rep

echo "PASS: malloc lab traces passed"
