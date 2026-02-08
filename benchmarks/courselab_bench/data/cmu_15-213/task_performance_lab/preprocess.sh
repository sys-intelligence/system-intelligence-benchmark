#!/bin/bash
# preprocess.sh - Setup script for Performance Lab
# Runs before the agent starts. Calibrates baseline CPEs and hashes infrastructure files.
set -e

cd /workspace

# Build the naive version to calibrate baseline CPEs for this system
make clean && make

# Run driver to measure actual naive CPE values on this machine
# The initial kernels.c has rotate() calling naive_rotate() and smooth() calling naive_smooth()
OUTPUT=$(./driver -t 2>&1 || true)

# Extract CPE values for the rotate function (initially wrapping naive_rotate)
# Output line format: "Your CPEs\t<v1>\t<v2>\t<v3>\t<v4>\t<v5>"
# awk fields: $1="Your" $2="CPEs" $3=v1 $4=v2 $5=v3 $6=v4 $7=v5
ROTATE_CPES=$(echo "$OUTPUT" | awk '/Version = rotate: Current/{found=1} found && /Your CPEs/{print; found=0}')
R64=$(echo "$ROTATE_CPES" | awk '{print $3}')
R128=$(echo "$ROTATE_CPES" | awk '{print $4}')
R256=$(echo "$ROTATE_CPES" | awk '{print $5}')
R512=$(echo "$ROTATE_CPES" | awk '{print $6}')
R1024=$(echo "$ROTATE_CPES" | awk '{print $7}')

# Extract CPE values for the smooth function (initially wrapping naive_smooth)
SMOOTH_CPES=$(echo "$OUTPUT" | awk '/Version = smooth: Current/{found=1} found && /Your CPEs/{print; found=0}')
S32=$(echo "$SMOOTH_CPES" | awk '{print $3}')
S64=$(echo "$SMOOTH_CPES" | awk '{print $4}')
S128=$(echo "$SMOOTH_CPES" | awk '{print $5}')
S256=$(echo "$SMOOTH_CPES" | awk '{print $6}')
S512=$(echo "$SMOOTH_CPES" | awk '{print $7}')

# Validate that we got values and update config.h with calibrated baselines
if [ -n "$R64" ] && [ -n "$S32" ]; then
    cat > config.h << EOF
/*********************************************************
 * config.h - Configuration data for the driver.c program.
 * Auto-calibrated baseline CPEs for this system.
 *********************************************************/
#ifndef _CONFIG_H_
#define _CONFIG_H_

#define R64    $R64
#define R128   $R128
#define R256   $R256
#define R512   $R512
#define R1024  $R1024

#define S32   $S32
#define S64   $S64
#define S128  $S128
#define S256  $S256
#define S512  $S512

#endif /* _CONFIG_H_ */
EOF
    echo "Baselines calibrated: R={$R64,$R128,$R256,$R512,$R1024} S={$S32,$S64,$S128,$S256,$S512}"
else
    echo "WARNING: Could not parse baseline CPEs, using defaults from config.h"
fi

# Clean build artifacts so the agent starts fresh
make clean

# Hash all infrastructure files to detect tampering
# The agent should only modify kernels.c
sha256sum driver.c defs.h config.h clock.c clock.h fcyc.c fcyc.h Makefile > .infrastructure.sha256
