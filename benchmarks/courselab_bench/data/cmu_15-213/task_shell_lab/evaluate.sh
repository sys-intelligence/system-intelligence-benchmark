#!/bin/bash
set -euo pipefail

# Check test files weren't tampered with
if ! sha256sum -c .tests.sha256 > /dev/null 2>&1; then
  echo "FAIL: test files were modified"
  exit 1
fi

# Build
make clean > /dev/null 2>&1 || true
make all > /dev/null 2>&1

if ! command -v perl > /dev/null 2>&1; then
  apt-get update -y > /dev/null 2>&1
  apt-get install -y perl > /dev/null 2>&1
fi

if [ ! -x ./tsh ]; then
  echo "FAIL: tsh was not built"
  exit 1
fi

if [ ! -x ./tshref ]; then
  echo "FAIL: tshref missing or not executable"
  exit 1
fi

TSHARGS="-p"
pass=1

normalize_output() {
  sed -E 's/\([0-9]+\)/(PID)/g'
}

for t in trace{01..16}.txt; do
  ./sdriver.pl -t "$t" -s ./tshref -a "$TSHARGS" > ".ref_${t}.out"
  ./sdriver.pl -t "$t" -s ./tsh -a "$TSHARGS" > ".out_${t}.log"
  normalize_output < ".ref_${t}.out" > ".ref_${t}.norm"
  normalize_output < ".out_${t}.log" > ".out_${t}.norm"
  if ! diff -u ".ref_${t}.norm" ".out_${t}.norm" > /dev/null; then
    echo "FAIL: $t output mismatch"
    pass=0
  fi
done

if [ "$pass" -eq 1 ]; then
  echo "PASS: All traces match reference output"
  exit 0
fi

exit 1
