#!/bin/bash
set -euo pipefail

echo "=== Evaluation ==="

cd /workspace/ostep-projects/filesystems-checker

echo "Verifying protected files were not modified"
if [ -f /tmp/checksums/protected.sha256 ]; then
  sha256sum -c /tmp/checksums/protected.sha256 || {
    echo "FAIL: Protected files were modified"
    exit 1
  }
fi
echo "All protected files unchanged"

if [ ! -f xcheck.c ]; then
  echo "FAIL: xcheck.c not found"
  exit 1
fi

echo "Building xcheck"
gcc -Wall -Werror -O2 -o xcheck xcheck.c

run_case() {
  local name=$1
  local cmd=$2
  local expected_rc=$3
  local expected_out=$4
  local expected_err=$5
  local stdout
  local stderr
  local rc

  set +e
  stdout=$(eval "$cmd" 2>"/tmp/${name}.err")
  rc=$?
  set -e

  stderr=$(cat "/tmp/${name}.err")
  stdout=$(printf "%s" "$stdout" | sed 's/[[:space:]]*$//')
  stderr=$(printf "%s" "$stderr" | sed 's/[[:space:]]*$//')

  if [ "$rc" -ne "$expected_rc" ]; then
    echo "FAIL: $name expected rc $expected_rc, got $rc"
    exit 1
  fi

  if [ "$stdout" != "$expected_out" ]; then
    echo "FAIL: $name unexpected stdout"
    echo "--- expected ---"
    printf "%s\n" "$expected_out"
    echo "--- actual ---"
    printf "%s\n" "$stdout"
    exit 1
  fi

  if [ "$stderr" != "$expected_err" ]; then
    echo "FAIL: $name unexpected stderr"
    echo "--- expected ---"
    printf "%s\n" "$expected_err"
    echo "--- actual ---"
    printf "%s\n" "$stderr"
    exit 1
  fi

  echo "PASS: $name"
}

run_case "usage" "./xcheck" 1 "" "Usage: xcheck <file_system_image>"
run_case "missing" "./xcheck tests/images/missing.img" 1 "" "image not found."
run_case "valid" "./xcheck tests/images/valid.img" 0 "" ""
run_case "bad_inode" "./xcheck tests/images/bad_inode.img" 1 "" "ERROR: bad inode."
run_case "bad_direct" "./xcheck tests/images/bad_direct.img" 1 "" "ERROR: bad direct address in inode."
run_case "bad_indirect" "./xcheck tests/images/bad_indirect.img" 1 "" "ERROR: bad indirect address in inode."
run_case "bad_root" "./xcheck tests/images/bad_root.img" 1 "" "ERROR: root directory does not exist."
run_case "bad_dirformat" "./xcheck tests/images/bad_dirformat.img" 1 "" "ERROR: directory not properly formatted."
run_case "bad_bitmap" "./xcheck tests/images/bad_bitmap.img" 1 "" "ERROR: address used by inode but marked free in bitmap."
run_case "bad_bitmap_marked" "./xcheck tests/images/bad_bitmap_marked.img" 1 "" "ERROR: bitmap marks block in use but it is not in use."
run_case "bad_direct_twice" "./xcheck tests/images/bad_direct_twice.img" 1 "" "ERROR: direct address used more than once."
run_case "bad_indirect_twice" "./xcheck tests/images/bad_indirect_twice.img" 1 "" "ERROR: indirect address used more than once."
run_case "bad_inode_referred" "./xcheck tests/images/bad_inode_referred.img" 1 "" "ERROR: inode referred to in directory but marked free."
run_case "bad_inode_unreferenced" "./xcheck tests/images/bad_inode_unreferenced.img" 1 "" "ERROR: inode marked use but not found in a directory."
run_case "bad_refcount" "./xcheck tests/images/bad_refcount.img" 1 "" "ERROR: bad reference count for file."
run_case "bad_dir_dup" "./xcheck tests/images/bad_dir_dup.img" 1 "" "ERROR: directory appears more than once in file system."

echo "PASS: All tests passed"
exit 0
