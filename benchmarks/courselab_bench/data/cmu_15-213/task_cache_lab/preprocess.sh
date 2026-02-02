#!/bin/bash
set -euo pipefail

export DEBIAN_FRONTEND=noninteractive
export DEBCONF_NONINTERACTIVE_SEEN=true

echo "=== Setting up CMU 15-213 Cache Lab ==="
cd /workspace

# 1. 更新 apt 源（可选：使用清华源加速）
if [ -f /etc/apt/sources.list ]; then
    sed -i 's/archive.ubuntu.com/mirrors.tuna.tsinghua.edu.cn/g' /etc/apt/sources.list
    sed -i 's/security.ubuntu.com/mirrors.tuna.tsinghua.edu.cn/g' /etc/apt/sources.list
fi

APT_OPTS=("-o" "Acquire::Retries=3" "-o" "Acquire::http::Timeout=20")
if ! apt-get "${APT_OPTS[@]}" update -y >/tmp/apt-update.log 2>&1; then
    cat /tmp/apt-update.log
    exit 1
fi
echo "APT update completed"
# Install apt-utils early to silence debconf and keep stderr clean
if ! apt-get "${APT_OPTS[@]}" install -y --no-install-recommends apt-utils ca-certificates >/tmp/apt-utils.log 2>&1; then
    cat /tmp/apt-utils.log
    exit 1
fi
dpkg -s apt-utils >/dev/null 2>&1 || {
    echo "ERROR: apt-utils missing after install"
    exit 1
}

# 2. 核心依赖（精简加速安装）
if ! apt-get "${APT_OPTS[@]}" install -y --no-install-recommends \
    build-essential \
    make \
    valgrind \
    python3 \
    >/tmp/apt-deps.log 2>&1; then
    cat /tmp/apt-deps.log
    exit 1
fi

# 3. 验证关键文件
required_files=("csim.c" "trans.c" "cachelab.c" "cachelab.h" "csim-ref" "test-csim" "test-trans.c" "tracegen.c" "driver.py" "Makefile" "traces")
for f in "${required_files[@]}"; do
    if [ ! -e "$f" ]; then
        echo "ERROR: missing required file $f"
        exit 1
    fi
    echo "  ✓ $f"
done

# 4. 权限处理：确保可执行
chmod +x csim-ref test-csim driver.py || true

# Record checksums for protected infra (not student solution files csim.c/trans.c)
mkdir -p /tmp/checksums
CHECKSUM_FILE=/tmp/checksums/protected.sha256
: > "$CHECKSUM_FILE"
protected_list=("cachelab.c" "cachelab.h" "csim-ref" "test-csim" "test-trans.c" "tracegen.c" "driver.py" "Makefile")
for f in "${protected_list[@]}"; do
    if [ -e "$f" ]; then
        sha256sum "$f" >> "$CHECKSUM_FILE"
        echo "  Protected: $f"
    fi
done
for f in traces/*; do
    if [ -f "$f" ]; then
        sha256sum "$f" >> "$CHECKSUM_FILE"
        echo "  Protected: $f"
    fi
done

echo "Setup complete"
exit 0
