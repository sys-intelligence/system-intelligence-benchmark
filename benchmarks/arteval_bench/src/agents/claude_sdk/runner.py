#!/usr/bin/env python3
"""Claude Agent SDK runner for ArtEvalBench.

This script uses Claude Agent SDK (ClaudeExecutor) to complete artifact evaluation tasks.
It is designed to run inside a Docker container where:
- The artifact repository is mounted at /repo
- This agent code is mounted at /agent
- The task description is passed as a command-line argument
"""

import asyncio
import os
import sys

# 添加 agent 目录下的 claude 和 sdk 到 Python 路径
sys.path.insert(0, '/agent')
sys.path.insert(0, '/agent/claude')

# 尝试导入 Claude Agent SDK
try:
    from claude_agent_sdk import query, ClaudeAgentOptions
    CLAUDE_SDK_AVAILABLE = True
except ImportError as e:
    print(f"ERROR: Failed to import claude_agent_sdk: {e}", file=sys.stderr)
    CLAUDE_SDK_AVAILABLE = False

# 尝试导入 message_formatter（可选）
try:
    from message_formatter import MessageFormatter
    FORMATTER_AVAILABLE = True
except ImportError:
    print("WARNING: message_formatter not available, will use basic output.", file=sys.stderr)
    FORMATTER_AVAILABLE = False

if not CLAUDE_SDK_AVAILABLE:
    print("ERROR: claude_agent_sdk is not available.", file=sys.stderr)
    print("Please ensure the SDK is properly installed in the container.", file=sys.stderr)
    sys.exit(1)


def get_default_work_dir():
    """获取工作目录提示。不硬编码路径，只从环境变量获取（如果设置了的话）。"""
    # 只从环境变量获取，不硬编码任何特定路径
    return os.environ.get('WORK_DIR', None)


async def run_agent(model_name: str, task_description: str):
    """使用 Claude Agent SDK 执行任务。
    
    Args:
        model_name: Claude 模型名称（如 claude-sonnet-4-5-20250929）
        task_description: 任务描述（包含 README 内容等）
    """
    # 获取工作目录提示（如果有环境变量的话，否则让 agent 自己探索）
    work_dir_hint = get_default_work_dir()
    
    # 基础 system prompt
    work_dir_instruction = ""
    if work_dir_hint:
        work_dir_instruction = f"- You may start by checking: {work_dir_hint}\n"
    
    base_prompt = f"""You are an experienced software engineer.

ENVIRONMENT SETUP:
- You are running inside a Docker container with root permissions.
- The artifact repository should be in the current working directory or nearby.
- You should explore the directory structure to find the artifact repository.
{work_dir_instruction}- You have access to Read, Write, and Bash tools to complete the task.

YOUR TASK:
{task_description}

IMPORTANT GUIDELINES:
1. First, explore the current directory structure to understand where you are and where the artifact is located.
2. Navigate to the artifact repository root directory.
3. If you see 'sudo' in any instructions, remove it (you already have root access).
4. Do NOT attempt to switch git branches (you are already on the correct branch).
5. Follow the README instructions step by step.
6. Use the Bash tool to run commands, Read tool to inspect files, and Write tool to create/modify files.
7. Work systematically through environment setup, build/install, benchmark preparation, and experiment execution.
8. If you encounter errors, try to debug and resolve them using the available tools."""
    
    # 不在 agent 侧提示评估流程，避免泄露答案
    system_prompt = base_prompt

    # 配置 Claude Agent 选项
    options = ClaudeAgentOptions(
        system_prompt=system_prompt,
        allowed_tools=["Read", "Write", "Bash"],  # 使用标准工具
    )
    
    # 使用 message_formatter 打印美化输出（如果可用）
    formatter = None
    if FORMATTER_AVAILABLE:
        try:
            formatter = MessageFormatter()
            formatter.print_header()
        except Exception as e:
            print(f"WARNING: Failed to initialize MessageFormatter: {e}", file=sys.stderr)
    
    print(f"\n{'='*60}", flush=True)
    print(f"Starting Claude Agent SDK with model: {model_name}", flush=True)
    print(f"Task: {task_description[:200]}..." if len(task_description) > 200 else f"Task: {task_description}", flush=True)
    print(f"{'='*60}\n", flush=True)
    
    try:
        # 发起查询并处理消息流
        # 注意：这里的 prompt 可以是一个简单的启动指令，
        # 因为 system_prompt 已经包含了完整的任务描述
        result_text = ""
        message_count = 0
        
        # 发起查询并处理消息流
        async for message in query(
            prompt="Please start working on the artifact evaluation task described in the system prompt. Begin by changing to the artifact repository directory and examining the README or instructions.",
            options=options
        ):
            message_count += 1
            # 每10条消息输出一次进度，确保外部知道程序还在运行
            if message_count % 10 == 0:
                print(f"[Progress] Processed {message_count} messages...", flush=True)
            
            # 格式化并打印每条消息
            if formatter:
                try:
                    formatter.format_message(message)
                except Exception as e:
                    print(f"WARNING: Failed to format message: {e}", file=sys.stderr, flush=True)
                    print(str(message), flush=True)
            else:
                # 如果没有 formatter，简单打印消息
                print(str(message), flush=True)
            
            # 保存最后的消息
            msg_str = str(message)
            if 'ResultMessage' in msg_str or 'TextBlock' in msg_str:
                # 尝试提取文本内容（虽然在这个场景下我们主要关心工具调用的副作用）
                result_text = msg_str
        
        if formatter:
            formatter.print_footer()
        
        print(f"\n{'='*60}", flush=True)
        print(f"Claude Agent SDK execution completed. Total messages: {message_count}", flush=True)
        print(f"{'='*60}\n", flush=True)
        
        # 打印最后的 API 元数据（成本、token 等）
        if formatter:
            try:
                metadata = formatter.get_api_metadata()
                if metadata:
                    print(f"\nAPI Usage Metadata:", flush=True)
                    print(f"  Input tokens: {metadata.get('input_tokens', 'N/A')}", flush=True)
                    print(f"  Output tokens: {metadata.get('output_tokens', 'N/A')}", flush=True)
                    print(f"  Total cost: ${metadata.get('total_cost', 'N/A')}", flush=True)
            except Exception as e:
                print(f"WARNING: Failed to get metadata: {e}", file=sys.stderr, flush=True)
        
        return 0  # 成功完成
        
    except asyncio.TimeoutError as e:
        print(f"\nERROR: Claude Agent SDK execution timed out: {e}", file=sys.stderr, flush=True)
        print(f"Processed {message_count} messages before timeout.", file=sys.stderr, flush=True)
        if formatter:
            formatter.print_footer()
        return 1  # 失败
    except Exception as e:
        print(f"\nERROR: Claude Agent SDK execution failed: {e}", file=sys.stderr, flush=True)
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.stderr.flush()
        if formatter:
            formatter.print_footer()
        return 1  # 失败


def main():
    """主入口函数。"""
    if len(sys.argv) != 3:
        print("Usage: python3 runner.py <model_name> <task_description>", file=sys.stderr)
        print("Example: python3 runner.py claude-sonnet-4-5-20250929 'Install and run tests'", file=sys.stderr)
        sys.exit(1)
    
    model_name = sys.argv[1]
    task_description = sys.argv[2]
    
    # 确保 ANTHROPIC_API_KEY 环境变量已设置
    if not os.environ.get('ANTHROPIC_API_KEY'):
        print("ERROR: ANTHROPIC_API_KEY environment variable is not set.", file=sys.stderr)
        print("Please ensure the API key is properly configured.", file=sys.stderr)
        sys.exit(1)
    
    # 运行异步主函数，添加超时控制（30分钟 = 1800秒）
    try:
        exit_code = asyncio.run(
            asyncio.wait_for(
                run_agent(model_name, task_description),
                timeout=3600.0  # 30分钟超时
            )
        )
    except asyncio.TimeoutError:
        print("ERROR: Agent execution exceeded 30 minute timeout.", file=sys.stderr, flush=True)
        sys.exit(1)
    except Exception as e:
        print(f"ERROR: Failed to run agent: {e}", file=sys.stderr, flush=True)
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.stderr.flush()
        sys.exit(1)
    
    sys.exit(exit_code)


if __name__ == '__main__':
    main()
