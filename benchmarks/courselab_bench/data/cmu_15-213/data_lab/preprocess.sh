#!/bin/bash
set -e

echo "=== Preprocessing Data Lab ==="

# Make dlc executable
chmod +x dlc

# Install required packages for compilation
# gcc-multilib is required for -m32 flag (32-bit compilation)
# libc6-dev-i386 provides 32-bit C library headers
apt-get update -qq
apt-get install -y -qq build-essential gcc-multilib make perl libc6-dev-i386 > /dev/null

# Clean any existing build artifacts
make clean 2>/dev/null || true

# Verify all required files are present
required_files="bits.c bits.h btest.c btest.h decl.c tests.c dlc Makefile"
for file in $required_files; do
    if [ ! -f "$file" ]; then
        echo "ERROR: Required file $file is missing"
        exit 1
    fi
done

echo "All required files present"

# Create checksums for files that should NOT be modified
# Only bits.c and bits.h are allowed to be modified
echo "Creating checksums for protected files..."
protected_files="btest.c btest.h decl.c tests.c dlc driver.pl Driverhdrs.pm Driverlib.pm fshow.c ishow.c Makefile README"

# Create checksum file
rm -f .protected_checksums
for file in $protected_files; do
    if [ -f "$file" ]; then
        md5sum "$file" >> .protected_checksums
    fi
done

echo "Checksums created for protected files"
echo "Preprocessing complete"
exit 0
