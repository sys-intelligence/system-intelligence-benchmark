#!/usr/bin/env python3
"""
Claude Agent SDK runner for ArtEvalBench - Host Machine Version

This script runs directly on the host machine WITHOUT Docker-in-Docker.
Use this when:
- You need multi-node Kind clusters (which don't work well in DinD)
- You want better performance and fewer compatibility issues
- Docker is already installed and running on your host

Usage:
    python3 run_on_host.py --artifact-path /path/to/artifact --task "Your task description"
    
    OR use the default Acto artifact:
    python3 run_on_host.py --use-acto-default

Prerequisites (install on host):
    - Docker (running)
    - Python 3.8+
    - Go 1.18+
    - Kind (kubernetes in docker)
    - kubectl
    - claude-agent-sdk (pip install claude-agent-sdk)
    - ANTHROPIC_API_KEY environment variable set
"""

import argparse
import asyncio
import os
import sys
from pathlib import Path

# Try to import Claude Agent SDK
try:
    from claude_agent_sdk import query, ClaudeAgentOptions
    CLAUDE_SDK_AVAILABLE = True
except ImportError as e:
    print(f"ERROR: Failed to import claude_agent_sdk: {e}", file=sys.stderr)
    print("Please install it: pip install claude-agent-sdk", file=sys.stderr)
    CLAUDE_SDK_AVAILABLE = False
    sys.exit(1)


def get_acto_default_task():
    """Return the default Acto artifact evaluation task."""
    return """Complete the artifact evaluation for the Acto research paper (SOSP 2023).

The artifact repository should be at the path specified. Follow these steps:

STEP 1: Navigate to the artifact directory and examine the structure
- The main repository contains the Acto tool
- Check for README.md or similar documentation

STEP 2: Follow the README instructions to:
1. Install all prerequisites (Python dependencies, Go, Kind, kubectl)
2. Configure system settings (inotify limits if needed)
3. Build dependent modules using 'make'

STEP 3: Run the experiments:
1. First, run the kick-the-tire test: python3 reproduce_bugs.py --bug-id rbop-928
   This should take about 10-20 minutes.
2. After kick-the-tire succeeds, run the full experiments as described in README.

IMPORTANT NOTES:
- You are running on the HOST machine, not inside Docker
- Docker is already installed and running on this host
- You have root/sudo access if needed
- Kind clusters will be created directly on the host Docker (not nested)
- Long-running commands are expected - do not interrupt them

If you encounter errors, debug and resolve them systematically."""


def get_system_prompt(artifact_path: str, task: str) -> str:
    """Generate the system prompt for the agent."""
    return f"""You are an experienced software engineer completing an artifact evaluation task.

ENVIRONMENT SETUP (HOST MACHINE - NOT DOCKER):
- You are running DIRECTLY on the host machine (NOT inside a Docker container)
- Docker daemon is already running on this host
- When you use Kind to create Kubernetes clusters, they will be created using the host's Docker
- This avoids Docker-in-Docker compatibility issues
- You may need sudo for some operations

ARTIFACT LOCATION:
- The artifact repository is located at: {artifact_path}
- Start by changing to this directory: cd {artifact_path}

YOUR TASK:
{task}

TIMEOUT CONFIGURATION (CRITICAL):
- Long-running commands (builds, tests, Kind cluster creation) are expected
- DO NOT set short timeouts - let commands complete naturally
- Kind cluster creation can take 5-10 minutes
- Full benchmark runs can take hours

IMPORTANT GUIDELINES:
1. First, cd to {artifact_path} and examine the directory structure
2. Follow the README instructions step by step
3. If you see 'sudo' in instructions, you can use it (or skip if already root)
4. Use the Bash tool to run commands, Read tool to inspect files
5. Work systematically through setup, build, and experiment execution
6. If you encounter errors, debug and resolve them using available tools
7. For Kind clusters, they will work properly since you're on the host (not DinD)"""


async def run_agent(artifact_path: str, task: str, model: str = "claude-sonnet-4-5-20250929"):
    """Run the Claude Agent SDK on the host machine."""
    
    system_prompt = get_system_prompt(artifact_path, task)
    
    options = ClaudeAgentOptions(
        system_prompt=system_prompt,
        allowed_tools=["Read", "Write", "Bash"],
        setting_sources=["user"],  # Load ~/.claude/settings.json for timeout config
    )
    
    print(f"\n{'='*70}", flush=True)
    print(f"Starting Claude Agent SDK (Host Mode)", flush=True)
    print(f"Model: {model}", flush=True)
    print(f"Artifact Path: {artifact_path}", flush=True)
    print(f"{'='*70}\n", flush=True)
    
    try:
        message_count = 0
        
        async for message in query(
            prompt=f"Please start the artifact evaluation task. Begin by changing to the artifact directory at {artifact_path} and examining its contents.",
            options=options
        ):
            message_count += 1
            
            if message_count % 10 == 0:
                print(f"[Progress] Processed {message_count} messages...", flush=True)
            
            # Print each message
            print(str(message), flush=True)
        
        print(f"\n{'='*70}", flush=True)
        print(f"Execution completed. Total messages: {message_count}", flush=True)
        print(f"{'='*70}\n", flush=True)
        
        return 0
        
    except Exception as e:
        print(f"\nERROR: Execution failed: {e}", file=sys.stderr, flush=True)
        import traceback
        traceback.print_exc(file=sys.stderr)
        return 1


def check_prerequisites():
    """Check that required tools are available on the host."""
    import shutil
    
    missing = []
    
    # Check Docker
    if not shutil.which("docker"):
        missing.append("docker")
    
    # Check Python
    if not shutil.which("python3"):
        missing.append("python3")
    
    # Check pip
    if not shutil.which("pip3") and not shutil.which("pip"):
        missing.append("pip3")
    
    # Optional: check for Go, Kind, kubectl (these can be installed by the agent)
    optional_missing = []
    if not shutil.which("go"):
        optional_missing.append("go")
    if not shutil.which("kind"):
        optional_missing.append("kind")
    if not shutil.which("kubectl"):
        optional_missing.append("kubectl")
    
    if missing:
        print(f"ERROR: Required tools not found: {', '.join(missing)}", file=sys.stderr)
        print("Please install them before running this script.", file=sys.stderr)
        return False
    
    if optional_missing:
        print(f"NOTE: Optional tools not found (agent will install if needed): {', '.join(optional_missing)}")
    
    # Check Docker is running
    import subprocess
    try:
        result = subprocess.run(["docker", "ps"], capture_output=True, timeout=10)
        if result.returncode != 0:
            print("ERROR: Docker is not running. Please start Docker first.", file=sys.stderr)
            return False
    except Exception as e:
        print(f"ERROR: Cannot verify Docker status: {e}", file=sys.stderr)
        return False
    
    # Check API key
    if not os.environ.get("ANTHROPIC_API_KEY"):
        print("ERROR: ANTHROPIC_API_KEY environment variable is not set.", file=sys.stderr)
        return False
    
    print("All prerequisites check passed.", flush=True)
    return True


def setup_claude_settings():
    """Set up ~/.claude/settings.json with timeout configuration."""
    claude_dir = Path.home() / ".claude"
    settings_file = claude_dir / "settings.json"
    
    claude_dir.mkdir(exist_ok=True)
    
    settings = {
        "env": {
            "BASH_MAX_TIMEOUT_MS": "172800000",  # 48 hours
            "BASH_DEFAULT_TIMEOUT_MS": "172800000"
        }
    }
    
    import json
    with open(settings_file, 'w') as f:
        json.dump(settings, f, indent=2)
    
    print(f"Created {settings_file} with 48-hour timeout configuration.")


def main():
    parser = argparse.ArgumentParser(
        description="Run Claude Agent SDK for artifact evaluation on host machine",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )
    
    parser.add_argument(
        "--artifact-path",
        type=str,
        help="Path to the artifact repository on the host machine"
    )
    
    parser.add_argument(
        "--task",
        type=str,
        help="Task description for the agent"
    )
    
    parser.add_argument(
        "--use-acto-default",
        action="store_true",
        help="Use the default Acto artifact path and task"
    )
    
    parser.add_argument(
        "--model",
        type=str,
        default="claude-sonnet-4-5-20250929",
        help="Claude model to use (default: claude-sonnet-4-5-20250929)"
    )
    
    parser.add_argument(
        "--skip-prereq-check",
        action="store_true",
        help="Skip prerequisite checks"
    )
    
    args = parser.parse_args()
    
    # Determine artifact path and task
    if args.use_acto_default:
        # Default Acto artifact path
        script_dir = Path(__file__).parent.resolve()
        artifact_path = script_dir.parent.parent.parent / "data" / "benchmark" / "sosp23_acto" / "acto"
        artifact_path = str(artifact_path.resolve())
        task = get_acto_default_task()
        print(f"Using default Acto artifact path: {artifact_path}")
    elif args.artifact_path:
        artifact_path = os.path.abspath(args.artifact_path)
        task = args.task or get_acto_default_task()
    else:
        parser.error("Either --artifact-path or --use-acto-default must be specified")
    
    # Verify artifact path exists
    if not os.path.isdir(artifact_path):
        print(f"ERROR: Artifact path does not exist: {artifact_path}", file=sys.stderr)
        sys.exit(1)
    
    # Check prerequisites
    if not args.skip_prereq_check:
        if not check_prerequisites():
            sys.exit(1)
    
    # Setup Claude settings
    setup_claude_settings()
    
    # Set environment variables for Bash timeout
    os.environ['BASH_MAX_TIMEOUT_MS'] = '172800000'
    os.environ['BASH_DEFAULT_TIMEOUT_MS'] = '172800000'
    
    # Run the agent
    try:
        exit_code = asyncio.run(run_agent(artifact_path, task, args.model))
    except KeyboardInterrupt:
        print("\nInterrupted by user.", file=sys.stderr)
        sys.exit(130)
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc(file=sys.stderr)
        sys.exit(1)
    
    sys.exit(exit_code)


if __name__ == "__main__":
    main()
