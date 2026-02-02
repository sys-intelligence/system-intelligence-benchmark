#!/bin/bash
set -euo pipefail

echo "=== Evaluation ==="

cd /workspace/ostep-projects/concurrency-mapreduce

echo "Verifying protected files were not modified"
if [ -f /tmp/checksums/protected.sha256 ]; then
  sha256sum -c /tmp/checksums/protected.sha256 || {
    echo "FAIL: Protected files were modified"
    exit 1
  }
fi
echo "All protected files unchanged"

if [ ! -f mapreduce.c ]; then
  echo "FAIL: mapreduce.c not found"
  exit 1
fi

echo "Building mapreduce library"
gcc -Wall -Werror -pthread -O2 -c mapreduce.c -o mapreduce.o

echo "Building tests"
gcc -Wall -Werror -pthread -O2 -I. -o mr_wordcount mapreduce.o tests/mr_wordcount.c
gcc -Wall -Werror -pthread -O2 -I. -o mr_copytest mapreduce.o tests/mr_copytest.c

run_test() {
  local name=$1
  local cmd=$2
  local expected=$3
  local output
  local rc

  set +e
  output=$(eval "$cmd" 2>"/tmp/${name}.err")
  rc=$?
  set -e

  if [ $rc -ne 0 ]; then
    echo "FAIL: $name test exited with code $rc"
    cat "/tmp/${name}.err" || true
    exit 1
  fi

  output=$(printf "%s" "$output" | LC_ALL=C sort)

  if [ "$output" != "$expected" ]; then
    echo "FAIL: $name test produced unexpected output"
    echo "--- expected ---"
    printf "%s\n" "$expected"
    echo "--- actual ---"
    printf "%s\n" "$output"
    exit 1
  fi

  echo "PASS: $name"
}

expected_wordcount=$'bar 2\nbaz 3\nfoo 3'
run_test "wordcount" "./mr_wordcount tests/input1.txt tests/input2.txt" "$expected_wordcount"

expected_wordcount_2=$'bar 1\nfoo 2\nqux 3'
run_test "wordcount_tab" "./mr_wordcount tests/input3.txt" "$expected_wordcount_2"

expected_wordcount_empty=""
run_test "wordcount_empty" "./mr_wordcount tests/input_empty.txt" "$expected_wordcount_empty"

expected_copy=$'line_0 3\nline_1 5\nline_2 2'
run_test "copytest" "./mr_copytest tests/input_copy.txt" "$expected_copy"

expected_copy2=$'line_0 0\nline_1 1\nline_2 2'
run_test "copytest_short" "./mr_copytest tests/input_copy2.txt" "$expected_copy2"

echo "PASS: All tests passed"
exit 0
