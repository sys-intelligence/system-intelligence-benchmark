#!/usr/bin/env bash
set -euo pipefail

ASSIGNMENT="MP3"
GRADE_FILE_NAME="grade.txt"
TIME_OUT=1200
MAXIMUM_SCORE=100

# Run grader
timeout $TIME_OUT /opt/cs423/grade.sh "$ASSIGNMENT"

if [ ! -f "$WORKDIR/$GRADE_FILE_NAME" ]; then
  echo "FAIL: $GRADE_FILE_NAME not found"
  exit 2
fi

# Get score
TOTAL_SCORE="$(
  awk -F: '
    {
      rhs=$NF
      gsub(/\r/, "", rhs)
      if (match(rhs, /-?[0-9]+(\.[0-9]+)?/)) sum += substr(rhs, RSTART, RLENGTH)
    }
    END { if (sum == int(sum)) printf("%d\n", int(sum)); else printf("%.6f\n", sum); }
  ' "$WORKDIR/$GRADE_FILE_NAME"
)"
echo "TOTAL_SCORE=$TOTAL_SCORE"

# Pass or non pass
if [ "$TOTAL_SCORE" -ge "$MAXIMUM_SCORE" ]; then
  echo "PASS"
  exit 0
else
  echo "FAIL"
  exit 1
fi
