#!/bin/bash
set -euo pipefail

if ! sha256sum -c .test_files.sha256 > /dev/null 2>&1; then
  echo "FAIL: test files were modified"
  exit 1
fi

chmod +x driver.sh nop-server.py free-port.sh port-for-user.pl

make clean > /dev/null
make > /dev/null

./driver.sh | tee eval.log

score_line=$(grep -E "totalScore:" eval.log | tail -n 1 || true)
if [ -z "$score_line" ]; then
  echo "FAIL: no totalScore found"
  exit 1
fi

score=$(echo "$score_line" | sed -E 's/.*totalScore: ([0-9]+)\/([0-9]+).*/\1/')
max=$(echo "$score_line" | sed -E 's/.*totalScore: ([0-9]+)\/([0-9]+).*/\2/')

if [ "$score" = "$max" ]; then
  echo "PASS: proxy lab achieved full score"
  exit 0
fi

echo "FAIL: proxy lab score ${score}/${max}"
exit 1
