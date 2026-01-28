#!/bin/bash

# 注意：不要使用 set -e，因为某些命令可能返回非零退出码但不表示失败
# Print commands for debugging (可选，如果不需要可以注释掉)
# set -x

# set the model and task as parameters
if [ $# -ne 2 ]; then
    echo "Usage: $0 <model_location> <task_description>"
    echo "Example: $0 claude-sonnet-4-5-20250929 \"Install and run tests\""
    exit 1
fi

# 设置 API key（遵循其他 agent 的习惯，直接写死）
export ANTHROPIC_API_KEY="${ANTHROPIC_API_KEY}"

# 关闭 Python 缓冲，确保日志实时输出
export PYTHONUNBUFFERED=1

# 配置 Claude Agent SDK Bash 超时参数
# 48小时 = 172800000 毫秒
export BASH_MAX_TIMEOUT_MS=172800000
export BASH_DEFAULT_TIMEOUT_MS=172800000

# 调用 Python runner 脚本（-u 确保无缓冲输出）
# 注意：输出重定向由调用方处理（在 run_eval_in_env.py 中）
python3 -u /agent/runner.py "$1" "$2"

