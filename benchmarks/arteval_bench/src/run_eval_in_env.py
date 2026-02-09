"""Patch evaluator for running tests in a deployment."""

import asyncio
import json
import os
import re
import subprocess
import sys
from pathlib import Path

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../')))

from swerex.deployment.docker import DockerDeploymentConfig
from swerex.runtime.abstract import BashAction, Command, CreateBashSessionRequest, UploadRequest

from sdk.logger import logger


def _parse_eval_score(output) -> int:
    """Parse evaluation score from BashObservation or string output.

    - If a line is a single digit (e.g. '4', '0'), use it (prefer last such line).
    - If output contains 'Agent scores: {...}' (Oracle-style evaluator), count ': 1' as passed items.
    - Otherwise return 0.
    """
    s = (getattr(output, "output", None) or str(output) or "").strip()
    if not s:
        return 0
    lines = s.splitlines()
    for line in reversed(lines):
        t = line.strip()
        if t.isdigit():
            return int(t)
    m = re.search(r"Agent scores:\s*\{[^}]*\}", s)
    if m:
        return m.group(0).count(": 1")
    return 0


def write_to_file(file_path, content):
    """Write content to a file."""
    with open(file_path, 'w') as f:
        f.write(content)


def setup_claude_settings_on_host():
    """Set up ~/.claude/settings.json with timeout configuration on host."""
    claude_dir = Path.home() / ".claude"
    settings_file = claude_dir / "settings.json"
    
    claude_dir.mkdir(exist_ok=True)
    
    settings = {
        "env": {
            "BASH_MAX_TIMEOUT_MS": "172800000",  # 48 hours
            "BASH_DEFAULT_TIMEOUT_MS": "172800000"
        }
    }
    
    with open(settings_file, 'w') as f:
        json.dump(settings, f, indent=2)
    
    logger.info(f"Created {settings_file} with 48-hour timeout configuration.")


async def run_eval_on_host(project_path, task_id, task, model, agent_path, test_method, save_path):
    """Run evaluation directly on host machine (no Docker container).
    
    This is useful for tasks that require Kind clusters or other Docker-in-Docker
    scenarios that don't work well in nested containers.
    """
    logger.info("=" * 80)
    logger.info("Running evaluation directly on HOST MACHINE (not in Docker)")
    logger.info("=" * 80)
    
    # Check prerequisites
    import shutil
    
    if not shutil.which("docker"):
        raise RuntimeError("Docker is not installed on host")
    
    # Check if Docker is running
    result = subprocess.run(["docker", "ps"], capture_output=True, timeout=10)
    if result.returncode != 0:
        raise RuntimeError("Docker is not running on host")
    
    # Check API key
    if not os.environ.get("ANTHROPIC_API_KEY"):
        raise RuntimeError("ANTHROPIC_API_KEY environment variable is not set")
    
    # Setup Claude settings
    setup_claude_settings_on_host()
    
    # Ensure project path is absolute
    project_path = os.path.abspath(project_path)
    if not os.path.isdir(project_path):
        raise RuntimeError(f"Project path does not exist: {project_path}")
    
    logger.info(f"Project path: {project_path}")
    logger.info(f"Task ID: {task_id}")
    logger.info(f"Model: {model}")
    
    # Import Claude Agent SDK
    try:
        from claude_agent_sdk import query, ClaudeAgentOptions
    except ImportError as e:
        raise RuntimeError(f"claude_agent_sdk not installed: {e}. Install with: pip install claude-agent-sdk")
    
    # Build system prompt for host execution
    system_prompt = f"""You are an experienced software engineer completing an artifact evaluation task.

ENVIRONMENT SETUP (HOST MACHINE - NOT DOCKER):
- You are running DIRECTLY on the host machine (NOT inside a Docker container)
- Docker daemon is already running on this host
- When you use Kind to create Kubernetes clusters, they will be created using the host's Docker
- This avoids Docker-in-Docker compatibility issues
- You may need sudo for some operations

ARTIFACT LOCATION:
- The artifact repository is located at: {project_path}
- Start by changing to this directory: cd {project_path}

YOUR TASK:
{task}

TIMEOUT CONFIGURATION (CRITICAL):
- Long-running commands (builds, tests, Kind cluster creation) are expected
- DO NOT set short timeouts - let commands complete naturally
- Kind cluster creation can take 5-10 minutes
- Full benchmark runs can take hours

IMPORTANT GUIDELINES:
1. First, cd to {project_path} and examine the directory structure
2. Follow the README instructions step by step
3. If you see 'sudo' in instructions, you can use it (or skip if already root)
4. Use the Bash tool to run commands, Read tool to inspect files
5. Work systematically through setup, build, and experiment execution
6. If you encounter errors, debug and resolve them using available tools
7. For Kind clusters, they will work properly since you're on the host (not DinD)"""

    options = ClaudeAgentOptions(
        system_prompt=system_prompt,
        allowed_tools=["Read", "Write", "Bash"],
        setting_sources=["user"],  # Load ~/.claude/settings.json for timeout config
    )
    
    # Set environment variables
    os.environ['BASH_MAX_TIMEOUT_MS'] = '172800000'
    os.environ['BASH_DEFAULT_TIMEOUT_MS'] = '172800000'
    
    logger.info("Starting Claude Agent SDK (Host Mode)...")
    
    message_count = 0
    run_results_output = ""
    
    try:
        async for message in query(
            prompt=f"Please start the artifact evaluation task. Begin by changing to the artifact directory at {project_path} and examining its contents.",
            options=options
        ):
            message_count += 1
            
            if message_count % 10 == 0:
                logger.info(f"[Progress] Processed {message_count} messages...")
            
            # Log each message
            msg_str = str(message)
            logger.info(msg_str)
            
            if 'ResultMessage' in msg_str or 'TextBlock' in msg_str:
                run_results_output = msg_str
        
        logger.info(f"Claude Agent SDK execution completed. Total messages: {message_count}")
        
    except Exception as e:
        logger.error(f"Claude Agent SDK execution failed: {e}")
        import traceback
        traceback.print_exc()
        run_results_output = f"Error: {e}"
    
    # Run evaluation (test_method)
    logger.info("Running evaluation script...")
    try:
        # Change to project directory and run test
        eval_cmd = f"cd {project_path} && {test_method}"
        eval_result = subprocess.run(
            eval_cmd,
            shell=True,
            capture_output=True,
            text=True,
            timeout=300  # 5 minute timeout for evaluation
        )
        test_output = eval_result.stdout.strip()
        logger.info(f"Evaluation output: {test_output}")
        
        result = {
            'task': task,
            'project_path': project_path,
            'agent_run_results': run_results_output,
            'test_method': test_method,
            'score': int(test_output) if test_output.isdigit() else 0,
            'status': 'success',
            'run_on_host': True,
        }
    except Exception as e:
        logger.error(f"Error running test method: {e}")
        result = {
            'task': task,
            'project_path': project_path,
            'agent_run_results': run_results_output,
            'test_method': test_method,
            'score': 0,
            'status': f'error: {str(e)}',
            'run_on_host': True,
        }
    
    return result


async def run_eval_in_env(deployment, project_path, task_id, task, model, agent_path, test_method, save_path):
    """Spoiler: This function will work with any deployment."""
    await deployment.start()
    runtime = deployment.runtime

    if hasattr(runtime, "_config"):
        logger.info(f"Current RemoteRuntime timeout: {runtime._config.timeout}s")
        # 48 hours = 172800s (aligned with Bash command timeout)
        runtime._config.timeout = 172800.0
        logger.info(f"Overriding RemoteRuntime timeout to {runtime._config.timeout}s (48 hours)")

    # Issue a few one-off commands, similar to `subprocess.run()`
    logger.info(await runtime.execute(Command(command=['echo', 'Hello, world!'])))

    # Create a bash session
    await runtime.create_session(CreateBashSessionRequest())
    # Run a command in the session
    # The difference to the one-off commands is that environment state persists!
    logger.info(await runtime.run_in_session(BashAction(command="export MYVAR='test'")))
    logger.info(await runtime.run_in_session(BashAction(command='echo $MYVAR')))

    logger.info('Uploading project files...')
    logger.info(
        await runtime.upload(
            UploadRequest(
                source_path=project_path,
                target_path='/repo',
            )
        )
    )
    logger.info('Project files uploaded.')
    
    # For claude_sdk: remove eval script dirs so the agent cannot see evaluation logic
    is_claude_sdk = str(agent_path).endswith('claude_sdk')
    if is_claude_sdk:
        logger.info('Removing _agent_eval directories for claude_sdk to prevent answer leakage...')
        # Recursively find and remove all _agent_eval directories
        await runtime.run_in_session(
            BashAction(command='find /repo -type d -name "_agent_eval" -exec rm -rf {} + 2>/dev/null || true', timeout=30.0)
        )
        logger.info('_agent_eval directories removed.')
    
    run_results = await runtime.run_in_session(BashAction(command='cd /repo'))
    logger.info(run_results)
    run_results = await runtime.run_in_session(BashAction(command='pwd'))
    logger.info(f'Current directory: {run_results}')
    run_results = await runtime.run_in_session(BashAction(command='ls'))
    logger.info(f'Current directory contents: {run_results}')

    logger.info('Uploading agent runner script...')
    logger.info(
        await runtime.upload(
            UploadRequest(
                source_path=agent_path,
                target_path='/agent',
            )
        )
    )
    logger.info(await runtime.run_in_session(BashAction(command='ls /agent/runner.sh')))
    logger.info('Agent runner script uploaded.')

    logger.info('Setup the agent running environment...')
    logger.info(await runtime.run_in_session(BashAction(command='chmod +x /agent/runner.sh /agent/install.sh')))
    logger.info(await runtime.run_in_session(BashAction(command='cat /agent/runner.sh')))
    logger.info(await runtime.run_in_session(BashAction(command='/agent/install.sh')))
    
    # Set required env vars for claude_sdk (passed from host into container)
    if is_claude_sdk:
        anthropic_api_key = os.environ.get('ANTHROPIC_API_KEY')
        if anthropic_api_key:
            # Set env var in container bash session; use single quotes to avoid shell escaping
            escaped_key = anthropic_api_key.replace("'", "'\"'\"'")
            set_env_cmd = f"export ANTHROPIC_API_KEY='{escaped_key}'"
            logger.info('Setting ANTHROPIC_API_KEY in container...')
            logger.info(await runtime.run_in_session(BashAction(command=set_env_cmd)))
            # Verify env var is set
            verify_cmd = 'echo "ANTHROPIC_API_KEY is set: $([ -n "$ANTHROPIC_API_KEY" ] && echo yes || echo no)"'
            verify_res = await runtime.run_in_session(BashAction(command=verify_cmd))
            logger.info(f'Environment variable verification: {verify_res}')
        else:
            logger.warning('ANTHROPIC_API_KEY not found in host environment. Runner may fail.')

    logger.info('Running runner script...')
    # claude_sdk: longer timeout and live log streaming (other agents unchanged)
    runner_timeout = 172800.0 if is_claude_sdk else 1200.0  # 48h for claude_sdk

    if is_claude_sdk:
        # Live log monitoring: run runner in background, poll log file periodically
        await runtime.run_in_session(BashAction(command='rm -f /agent/runner.live.log && touch /agent/runner.live.log', timeout=10.0))

        start_cmd = (
            f'bash -c "stdbuf -oL -eL /agent/runner.sh \\"{model}\\" \\"{task}\\" > /agent/runner.live.log 2>&1 & '
            'RUNNER_PID=$!; '
            'sleep 1; '  # Ensure process has started
            'echo RUNNER_PID=$RUNNER_PID"'
        )
        start_res = await runtime.run_in_session(BashAction(command=start_cmd, timeout=30.0))
        start_output = str(getattr(start_res, "output", "")).strip()

        pid = None
        for line in start_output.split('\n'):
            if 'RUNNER_PID=' in line:
                pid = line.split('RUNNER_PID=', 1)[1].strip()
                break

        if not pid or not pid.isdigit():
            # Fallback: find PID by process name after short delay
            await asyncio.sleep(2)
            ps_res = await runtime.run_in_session(
                BashAction(command="ps aux | grep '[r]unner.py' | awk '{print $2}' | head -1", timeout=10.0)
            )
            pid = str(getattr(ps_res, "output", "")).strip()
        
        logger.info(f'claude_sdk runner started with pid: {pid}')

        await asyncio.sleep(2)  # Allow log file to have content

        elapsed = 0.0
        poll_interval = 10.0  # Poll every 10s for live log
        run_results = None
        last_log_content = ""  # Track last read content to avoid duplicate output

        while elapsed < runner_timeout:
            try:
                log_res = await runtime.run_in_session(
                    BashAction(command='cat /agent/runner.live.log 2>/dev/null || echo ""', timeout=30.0)
                )
                current_log_content = str(getattr(log_res, "output", "")).strip()

                if current_log_content and current_log_content != last_log_content:
                    if last_log_content and current_log_content.startswith(last_log_content):
                        new_content = current_log_content[len(last_log_content):].strip()
                        if new_content:
                            logger.info(f'[claude_sdk live log @ {elapsed:.0f}s ({elapsed/60:.1f} min)]\n{new_content}')
                    else:
                        logger.info(f'[claude_sdk live log @ {elapsed:.0f}s ({elapsed/60:.1f} min)]\n{current_log_content}')
                    last_log_content = current_log_content
                elif elapsed % 300 == 0 and elapsed > 0:
                    logger.info(f'[claude_sdk still running @ {elapsed:.0f}s ({elapsed/60:.1f} min), no new output]')
            except Exception as e:
                logger.info(f'Failed to read claude_sdk live log: {e}')

            if pid and pid.isdigit():
                ps_res = await runtime.run_in_session(
                    BashAction(command=f'ps -p {pid} >/dev/null 2>&1; echo $?', timeout=10.0)
                )
                ps_code = str(getattr(ps_res, "output", "")).strip()
                if ps_code != "0":
                    wait_res = await runtime.run_in_session(
                        BashAction(command=f'wait {pid} 2>/dev/null; echo $?', timeout=30.0)
                    )
                    exit_code_str = str(getattr(wait_res, "output", "")).strip()

                    class MockResult:
                        def __init__(self, code):
                            self.exit_code = int(code) if code.isdigit() else 0
                            self.output = f'exit_code={self.exit_code}'
                    run_results = MockResult(exit_code_str)
                    logger.info(f'claude_sdk runner finished with exit code: {run_results.exit_code}')
                    break
            else:
                ps_res = await runtime.run_in_session(
                    BashAction(command="ps aux | grep '[r]unner.py' | wc -l", timeout=10.0)
                )
                proc_count = str(getattr(ps_res, "output", "")).strip()
                if proc_count == "0" or not proc_count.isdigit() or int(proc_count) == 0:
                    logger.info('claude_sdk runner process not found, assuming finished')
                    class MockResult:
                        def __init__(self):
                            self.exit_code = 0
                            self.output = 'exit_code=0'
                    run_results = MockResult()
                    break

            await asyncio.sleep(poll_interval)
            elapsed += poll_interval

        if run_results is None:
            # Timeout: try to kill process and capture final log
            if pid and pid.isdigit():
                try:
                    await runtime.run_in_session(BashAction(command=f'kill -TERM {pid} 2>/dev/null || kill -9 {pid} 2>/dev/null || true', timeout=10.0))
                except Exception:
                    pass
            try:
                tail_log = await runtime.run_in_session(
                    BashAction(command='tail -n 200 /agent/runner.live.log', timeout=30.0)
                )
                logger.info(f'claude_sdk live log tail (on timeout):\n{tail_log}')
            except Exception as e:
                logger.info(f'Failed to read claude_sdk live log after timeout: {e}')
            raise TimeoutError(f'claude_sdk runner exceeded timeout {runner_timeout}s')

    else:
        runner_cmd = f'/agent/runner.sh "{model}" "{task}"'
        run_results = await runtime.run_in_session(BashAction(command=runner_cmd, timeout=runner_timeout))
    logger.info(f"agent's run results: {run_results}")
    logger.info('Runner script finished.')

    # For claude_sdk: upload eval scripts before running evaluation
    if is_claude_sdk:
        logger.info('Uploading _agent_eval directories for evaluation (claude_sdk)...')
        eval_dirs = []
        for root, dirs, files in os.walk(project_path):
            if '_agent_eval' in dirs:
                eval_source_path = os.path.join(root, '_agent_eval')
                rel_path = os.path.relpath(eval_source_path, project_path)
                eval_dirs.append((eval_source_path, rel_path))

        if eval_dirs:
            for eval_source_path, rel_path in eval_dirs:
                target_eval_path = os.path.join('/repo', rel_path)
                logger.info(f'Uploading _agent_eval from {eval_source_path} to {target_eval_path}')
                try:
                    await runtime.upload(
                        UploadRequest(
                            source_path=eval_source_path,
                            target_path=target_eval_path,
                        )
                    )
                    logger.info(f'_agent_eval directory uploaded: {rel_path}')
                except Exception as e:
                    logger.warning(f'Failed to upload _agent_eval from {eval_source_path}: {e}')
            logger.info('All _agent_eval directories uploaded for evaluation.')
        else:
            logger.warning(f'No _agent_eval directories found in {project_path}')

    try:
        test_output = await runtime.run_in_session(BashAction(command=test_method))
        logger.info(test_output)
        result = {
            'task': task,
            'project_path': project_path,
            'agent_run_results': run_results.output if hasattr(run_results, 'output') else str(run_results),
            'test_method': test_method,
            'score': _parse_eval_score(test_output),
            'status': 'success',
        }
    except Exception as e:
        logger.info(f'Error running test method: {e}')
        result = {
            'task': task,
            'project_path': project_path,
            'agent_run_results': run_results.output if hasattr(run_results, 'output') else str(run_results),
            'test_method': test_method,
            'score': 0,
            'status': f'error: {str(e)}',
        }

    # For claude_sdk: keep container running for inspection
    if is_claude_sdk:
        logger.info('=' * 80)
        logger.info('Keeping Docker container running for claude_sdk (for debugging purposes).')

        container_id = "unknown"
        container_name = "unknown"
        try:
            container_id_res = await runtime.run_in_session(
                BashAction(command='cat /etc/hostname 2>/dev/null || hostname 2>/dev/null || echo "unknown"', timeout=10.0)
            )
            container_id = str(getattr(container_id_res, "output", "")).strip()

            try:
                docker_info_res = await runtime.run_in_session(
                    BashAction(command='cat /proc/self/cgroup 2>/dev/null | grep docker | head -1 | cut -d/ -f3 | cut -c1-12 || echo ""', timeout=10.0)
                )
                docker_container_id = str(getattr(docker_info_res, "output", "")).strip()
                if docker_container_id:
                    container_id = docker_container_id
            except Exception:
                pass

            if hasattr(deployment, '_container_id'):
                container_id = deployment._container_id
            elif hasattr(deployment, 'container_id'):
                container_id = deployment.container_id
            if hasattr(deployment, '_container_name'):
                container_name = deployment._container_name
            elif hasattr(deployment, 'container_name'):
                container_name = deployment.container_name
        except Exception as e:
            logger.warning(f'Failed to get container information: {e}')
        
        logger.info(f'Container Information:')
        logger.info(f'  Container ID: {container_id}')
        logger.info(f'  Container Name: {container_name}')
        logger.info(f'  Task ID: {task_id}')
        logger.info(f'  Project Path: {project_path}')
        logger.info(f'  To inspect the container, use: docker exec -it {container_id} /bin/bash')
        logger.info(f'  Or find container by name/image and inspect manually')
        logger.info(f'  NOTE: Container will remain running. To stop it manually, use: docker stop {container_id}')
        logger.info(f'  WARNING: Remember to clean up containers to save storage space!')
        logger.info('=' * 80)

        result['container_id'] = container_id
        result['container_name'] = container_name
        result['container_kept'] = True
    else:
        await deployment.stop()
        result['container_kept'] = False
    
    return result


def run_eval(deployment, project_path, task_id, task, model, agent_path, test_method, save_path, run_on_host=False):
    """Run evaluation either on host or in Docker container.
    
    Args:
        deployment: Docker image to use (ignored if run_on_host=True)
        project_path: Path to the artifact project
        task_id: Task identifier
        task: Task description
        model: Model name
        agent_path: Path to agent scripts
        test_method: Evaluation command
        save_path: Path to save results
        run_on_host: If True, run directly on host machine instead of Docker
    """
    
    if run_on_host:
        # Run directly on host machine (no Docker container)
        logger.info(f"Task {task_id} configured to run on HOST machine (run_on_host=True)")
        return asyncio.run(
            run_eval_on_host(project_path, task_id, task, model, agent_path, test_method, save_path)
        )
    
    # Run in Docker container (original behavior)
    image = deployment or 'bastoica/ae-agent-ubuntu24.04:latest'

    # Enable privileged mode for Docker-in-Docker scenarios (e.g., Kind clusters)
    # This is required for Kubernetes-based artifact evaluations like Acto
    # Additional args for cgroups v2 compatibility:
    # - --cgroupns=host: Share cgroup namespace with host (required for Kind in cgroups v2)
    # - Environment variables for Kind cgroups v2 compatibility
    config = DockerDeploymentConfig(
        image=image,
        startup_timeout=1200.0,
        docker_args=[
            '--privileged',  # Required for Kind cluster creation
            '--cgroupns=host',  # Required for Kind nodes to start with cgroups v2
            '-e', 'KIND_EXPERIMENTAL_CONTAINERD_SNAPSHOTTER=native',  # Better cgroups v2 support
        ],
    )
    deployment_obj = config.get_deployment()

    return asyncio.run(
        run_eval_in_env(deployment_obj, project_path, task_id, task, model, agent_path, test_method, save_path)
    )



def test():
    task = 'The java is not installed. Can you please setup it? Note: you are in a docker with root permission. DO NOT use sudo.'
    project_path = '../data/benchmark/projects/test-repo'
    test_method = 'java -version'
    deployment = 'xuafeng/swe-go-python:latest'
    model = 'claude-sonnet-4-5-20250929'
    agent_path = './agents/claudecode'
    save_path = './eval_results'
    task_id = 'test_task_1'
    result = run_eval(deployment, project_path, task_id, task, model, agent_path, test_method, save_path)
    print('Test result:', result)


# TODO: still work on add openhand agent
def test1():
    task = 'The java is not installed. Can you please setup it? Note: you are in a docker with root permission. DO NOT use sudo.'
    project_path = '../data/benchmark/projects/test-repo'
    test_method = 'java -version'
    deployment = 'xuafeng/swe-go-python:latest'
    model = 'claude-sonnet-4-5-20250929'
    agent_path = './agents/openhand'
    save_path = './eval_results'
    task_id = 'test_task_1'
    result = run_eval(deployment, project_path, task_id, task, model, agent_path, test_method, save_path)
    print('Test result:', result)


def test2():
    task = "create a python file named hello.py that prints 'hello world'"
    project_path = '../data/benchmark/projects/test-repo'
    test_method = 'python hello.py'
    deployment = 'xuafeng/swe-go-python:latest'
    model = 'claude-sonnet-4-5-20250929'
    agent_path = './agents/claudecode'
    save_path = './eval_results'
    task_id = 'test_task_1'
    eval_out = asyncio.run(
        run_eval_in_env(deployment, project_path, task_id, task, model, agent_path, test_method, save_path)
    )
    print(eval_out)


if __name__ == '__main__':
    test1()
