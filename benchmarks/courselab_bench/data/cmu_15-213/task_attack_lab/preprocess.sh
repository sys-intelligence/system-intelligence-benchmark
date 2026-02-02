#!/bin/bash
set -euo pipefail

echo "=== Setting up CMU 15-213 Attack Lab ==="
cd /workspace

echo "Installing analysis tooling"
apt-get update
apt-get install -y build-essential gcc-multilib gdb binutils make python3 python3-pip

echo "Making binaries executable"
chmod +x ctarget rtarget hex2raw

echo "Disabling ASLR for deterministic addresses (best-effort)"
if sysctl -w kernel.randomize_va_space=0; then
    echo "ASLR disabled"
elif echo 0 > /proc/sys/kernel/randomize_va_space 2>/dev/null; then
    echo "ASLR disabled via /proc"
else
    echo "WARN: Could not disable ASLR (permissions?). Exploits may be unstable."
fi

echo "Verifying required files are present"
required_files="ctarget rtarget hex2raw cookie.txt farm.c README.txt"
for file in $required_files; do
    if [ ! -f "$file" ]; then
        echo "ERROR: Missing required file $file"
        exit 1
    fi
    echo "  ✓ $file"
done

echo "Creating checksums for protected files"
mkdir -p /tmp/checksums
CHECKSUM_FILE=/tmp/checksums/protected.sha256
: > "$CHECKSUM_FILE"
protected_files="$required_files"
for file in $protected_files; do
    sha256sum "$file" >> "$CHECKSUM_FILE"
    echo "  Protected: $file"
done

echo "Setup complete"
exit 0
