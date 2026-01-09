#!/bin/bash
set -e

echo "=== Preprocessing ==="

cd /workspace/processes-shell

mkdir -p /tmp/checksums
CHECKSUM_FILE=/tmp/checksums/protected.sha256
: > "$CHECKSUM_FILE"

PROTECTED_FILES=(
  "test-wish.sh"
)

for file in "${PROTECTED_FILES[@]}"; do
  if [ -f "$file" ]; then
    sha256sum "$file" >> "$CHECKSUM_FILE"
  fi
done

if [ -d tests ]; then
  find tests -type f | sort | while IFS= read -r file; do
    case "$file" in
      "tests/3.err"|"tests/3.out")
        continue
        ;;
    esac
    sha256sum "$file" >> "$CHECKSUM_FILE"
  done
fi

echo "Preprocessing complete"
exit 0
