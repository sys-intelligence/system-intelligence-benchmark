#!/bin/bash
# Preprocess: install dependencies and build Y86-64 toolchain
# NOTE: All stderr is redirected to stdout to prevent Inspect AI from
# treating harmless warnings (e.g. debconf) as fatal errors.
exec 2>&1
set -euo pipefail

export DEBIAN_FRONTEND=noninteractive

echo "=== Setting up CMU 15-213 Architecture Lab ==="
cd /workspace

# if [ -f /etc/apt/sources.list.d/debian.sources ]; then
#     sed -i 's@deb.debian.org@mirrors.tuna.tsinghua.edu.cn@g' /etc/apt/sources.list.d/debian.sources
# fi
sed -i 's|http://archive.ubuntu.com|http://mirrors.aliyun.com|g; s|http://security.ubuntu.com|http://mirrors.aliyun.com|g' /etc/apt/sources.list

# 1. Install core dependencies
apt-get update -y -qq
apt-get install -y -qq --no-install-recommends \
  build-essential gcc-multilib gdb binutils make \
  python3 perl bison flex libfl-dev ca-certificates

SIM_DIR="/workspace/sim"
if [ ! -d "$SIM_DIR" ]; then
    echo "ERROR: sim directory not found"; exit 1
fi

# 2. Patch Makefiles (Architecture Lab specific fixes)
echo "Patching Makefiles..."
# -fcommon: fix duplicate global variable definitions (GCC 10+)
# -lfl: replace old -ll to work with modern flex library
find "$SIM_DIR" -name "Makefile" -exec sed -i 's/^CFLAGS=.*/CFLAGS=-Wall -O1 -g -fcommon -Wno-error/g' {} +
find "$SIM_DIR" -name "Makefile" -exec sed -i 's/^LCFLAGS=.*/LCFLAGS=-O1 -fcommon/g' {} +
find "$SIM_DIR" -name "Makefile" -exec sed -i 's/-ll/-lfl/g' {} +

# Force-disable GUI options in all subdirectory Makefiles
for m in "$SIM_DIR/Makefile" "$SIM_DIR/pipe/Makefile" "$SIM_DIR/seq/Makefile" "$SIM_DIR/misc/Makefile"; do
    if [ -f "$m" ]; then
        sed -i 's/^GUIMODE=.*/GUIMODE=/' "$m"
        sed -i 's/^TKLIBS=.*/TKLIBS=/' "$m"
        sed -i 's/^TKINC=.*/TKINC=/' "$m"
    fi
done

# 3. Fix permissions on Perl scripts
find "$SIM_DIR" -name "*.pl" -exec chmod +x {} +

# 4. Clean any stale object files, then build Y86-64 tools
cd "$SIM_DIR"
make clean > /dev/null 2>&1 || true

if ! make all GUIMODE=; then
    echo "========= !! BUILD FAILED !! ========="
    exit 1
fi

# 4. Verify that critical tools were built
for f in misc/yas misc/yis pipe/psim; do
    if [ ! -f "$SIM_DIR/$f" ]; then
        echo "ERROR: $f not found after build"
        exit 1
    fi
done

echo "Setup complete"
exit 0