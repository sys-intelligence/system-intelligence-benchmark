#!/bin/bash

set -e  # Exit immediately on error.

echo "Installing Claude Agent SDK dependencies..."

# 确保 Python 3 和 pip 可用
apt-get update -y
apt-get install -y python3 python3-pip python3-venv git

# 安装 Claude Agent SDK
# 在 Ubuntu 24.04+ 的 Docker 容器中，需要使用 --break-system-packages 标志
# 因为 Python 3.12+ 有外部管理环境的保护（PEP 668）
# 注意：不要升级系统安装的 pip（由 Debian 包管理器安装），直接安装 SDK
pip3 install claude-agent-sdk --break-system-packages

# 如果 /agent 目录下有 sdk 文件夹（从宿主机上传），也添加到 Python 路径
# 这样可以使用项目里的自定义 SDK 模块
if [ -d "/agent/sdk" ]; then
    echo "Found local SDK in /agent/sdk, it will be available for import."
fi

# 配置 Claude Agent SDK Bash 超时参数
# 创建 ~/.claude/settings.json，48小时超时 = 172800000 毫秒
mkdir -p ~/.claude
cat > ~/.claude/settings.json << 'EOF'
{
  "env": {
    "BASH_MAX_TIMEOUT_MS": "172800000",
    "BASH_DEFAULT_TIMEOUT_MS": "172800000"
  }
}
EOF
echo "Created ~/.claude/settings.json with Bash timeout configuration (48 hours)."

echo "Claude Agent SDK installation completed successfully."
