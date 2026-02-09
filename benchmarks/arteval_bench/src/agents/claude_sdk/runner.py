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

# Add agent claude/sdk paths for imports
sys.path.insert(0, '/agent')
sys.path.insert(0, '/agent/claude')

try:
    from claude_agent_sdk import query, ClaudeAgentOptions
    CLAUDE_SDK_AVAILABLE = True
except ImportError as e:
    print(f"ERROR: Failed to import claude_agent_sdk: {e}", file=sys.stderr)
    CLAUDE_SDK_AVAILABLE = False

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
    """Return work dir hint from env only (no hardcoded paths)."""
    return os.environ.get('WORK_DIR', None)


async def run_agent(model_name: str, task_description: str):
    """Run the artifact evaluation task with Claude Agent SDK.

    Args:
        model_name: Claude model name (e.g. claude-sonnet-4-5-20250929).
        task_description: Task description (e.g. README content).
    """
    work_dir_hint = get_default_work_dir()
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

TIMEOUT CONFIGURATION (CRITICAL):
- The system has been configured with a 48-hour (172800000 ms) default Bash timeout.
- DO NOT specify timeout parameters in your Bash commands - the system default will be used automatically.
- Long-running commands (builds, tests, benchmarks) can take hours - this is normal and expected.
- If a command seems to be running long, DO NOT cancel or re-run it. Wait for completion.

IMPORTANT GUIDELINES:
1. First, explore the current directory structure to understand where you are and where the artifact is located.
2. Navigate to the artifact repository root directory.
3. If you see 'sudo' in any instructions, remove it (you already have root access).
4. Do NOT attempt to switch git branches (you are already on the correct branch).
5. Follow the README instructions step by step.
6. Use the Bash tool to run commands, Read tool to inspect files, and Write tool to create/modify files.
7. Work systematically through environment setup, build/install, benchmark preparation, and experiment execution.
8. If you encounter errors, try to debug and resolve them using the available tools.
9. For long-running commands, let them complete naturally. Do NOT set short timeouts or interrupt them."""

    system_prompt = base_prompt  # Do not hint evaluation flow to avoid leaking answers

    # setting_sources must be set so SDK loads timeout from ~/.claude/settings.json
    # See https://platform.claude.com/docs/en/agent-sdk/python#types
    options = ClaudeAgentOptions(
        system_prompt=system_prompt,
        allowed_tools=["Read", "Write", "Bash"],
        setting_sources=["user"],
    )

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
        result_text = ""
        message_count = 0

        async for message in query(
            prompt="Please start working on the artifact evaluation task described in the system prompt. Begin by changing to the artifact repository directory and examining the README or instructions.",
            options=options
        ):
            message_count += 1
            if message_count % 10 == 0:
                print(f"[Progress] Processed {message_count} messages...", flush=True)
            
            if formatter:
                try:
                    formatter.format_message(message)
                except Exception as e:
                    print(f"WARNING: Failed to format message: {e}", file=sys.stderr, flush=True)
                    print(str(message), flush=True)
            else:
                print(str(message), flush=True)

            msg_str = str(message)
            if 'ResultMessage' in msg_str or 'TextBlock' in msg_str:
                result_text = msg_str
        
        if formatter:
            formatter.print_footer()
        
        print(f"\n{'='*60}", flush=True)
        print(f"Claude Agent SDK execution completed. Total messages: {message_count}", flush=True)
        print(f"{'='*60}\n", flush=True)
        
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
        
        return 0

    except asyncio.TimeoutError as e:
        print(f"\nERROR: Claude Agent SDK execution timed out: {e}", file=sys.stderr, flush=True)
        print(f"Processed {message_count} messages before timeout.", file=sys.stderr, flush=True)
        if formatter:
            formatter.print_footer()
        return 1
    except Exception as e:
        print(f"\nERROR: Claude Agent SDK execution failed: {e}", file=sys.stderr, flush=True)
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.stderr.flush()
        if formatter:
            formatter.print_footer()
        return 1


def main():
    """Entry point."""
    if len(sys.argv) != 3:
        print("Usage: python3 runner.py <model_name> <task_description>", file=sys.stderr)
        print("Example: python3 runner.py claude-sonnet-4-5-20250929 'Install and run tests'", file=sys.stderr)
        sys.exit(1)
    
    model_name = sys.argv[1]
    task_description = sys.argv[2]
    
    if not os.environ.get('ANTHROPIC_API_KEY'):
        print("ERROR: ANTHROPIC_API_KEY environment variable is not set.", file=sys.stderr)
        print("Please ensure the API key is properly configured.", file=sys.stderr)
        sys.exit(1)
    
    # 48h = 172800000 ms (fallback if not set by shell)
    if not os.environ.get('BASH_MAX_TIMEOUT_MS'):
        os.environ['BASH_MAX_TIMEOUT_MS'] = '172800000'
    if not os.environ.get('BASH_DEFAULT_TIMEOUT_MS'):
        os.environ['BASH_DEFAULT_TIMEOUT_MS'] = '172800000'
    
    try:
        exit_code = asyncio.run(
            asyncio.wait_for(
                run_agent(model_name, task_description),
                timeout=172800.0,  # 48h
            )
        )
    except asyncio.TimeoutError:
        print("ERROR: Agent execution exceeded 48 hour timeout.", file=sys.stderr, flush=True)
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
