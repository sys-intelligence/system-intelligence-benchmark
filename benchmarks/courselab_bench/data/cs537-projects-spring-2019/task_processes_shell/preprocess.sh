#!/bin/bash
set -e

echo "=== Setting up CS537 Processes Shell Project ==="

cd /workspace

echo "Installing git"
apt-get update > /dev/null 2>&1
apt-get install -y git > /dev/null 2>&1

echo "Cloning ostep-projects repository"
git clone https://github.com/remzi-arpacidusseau/ostep-projects.git > /dev/null 2>&1
cd ostep-projects
git checkout 76cff3f89f4bf337af6e02e53a831b7eeb1396df > /dev/null 2>&1

echo "Removing git history"
rm -rf .git

echo "Creating checksums for protected files"
cd processes-shell

mkdir -p /tmp/checksums
CHECKSUM_FILE=/tmp/checksums/protected.sha256
: > "$CHECKSUM_FILE"

PROTECTED_FILES=(
  "test-wish.sh"
)

for file in "${PROTECTED_FILES[@]}"; do
  if [ -f "$file" ]; then
    sha256sum "$file" >> "$CHECKSUM_FILE"
    echo "  Protected: $file"
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
    echo "  Protected: $file"
  done
fi

echo "Setup complete"
exit 0
