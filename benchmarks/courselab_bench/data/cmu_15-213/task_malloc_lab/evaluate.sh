#!/bin/bash
set -euo pipefail

# Verify read-only files were not modified by the agent.
if [ -f .readonly_hashes ]; then
  if ! sha256sum -c .readonly_hashes > /dev/null 2>&1; then
    echo "FAIL: read-only files were modified"
    exit 1
  fi
fi

make clean > /dev/null 2>&1 || true
make > /dev/null 2>&1

MIN_PERF=100

for trace in short1-bal.rep short2-bal.rep; do
  echo "=== Running $trace ==="
  OUTPUT=$(./mdriver -V -f "$trace" 2>&1)
  echo "$OUTPUT"

  # Extract "Perf index = ... = XX/100" from mdriver output
  PERF=$(echo "$OUTPUT" | grep -oP 'Perf index = .* = \K[0-9]+(?=/100)')
  if [ -z "$PERF" ]; then
    echo "FAIL: could not parse Perf index from $trace"
    exit 1
  fi
  if [ "$PERF" -lt "$MIN_PERF" ]; then
    echo "FAIL: $trace Perf index $PERF < $MIN_PERF"
    exit 1
  fi
  echo "OK: $trace Perf index $PERF >= $MIN_PERF"
done

echo "PASS: malloc lab traces passed"
