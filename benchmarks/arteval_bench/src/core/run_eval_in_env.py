"""Patch evaluator for running tests in a deployment."""

import asyncio
import os
import re
import shlex

from swerex.deployment.docker import DockerDeploymentConfig
from swerex.runtime.abstract import BashAction, Command, CreateBashSessionRequest, UploadRequest

from sdk.logger import logger


def write_to_file(file_path, content):
    """Write content to a file."""
    with open(file_path, 'w') as f:
        f.write(content)


def _extract_output(result) -> str:
    output = getattr(result, 'output', result)
    return str(output).strip()


def _parse_score(output: str) -> int:
    if output.isdigit():
        return int(output)
    # Common evaluator output may include logs with the score on the last line.
    numbers = re.findall(r'-?\d+', output)
    return int(numbers[-1]) if numbers else 0


async def run_eval_in_env(deployment, project_path, task_id, task, model, agent_path, test_method, save_path):
    """Spoiler: This function will work with any deployment."""
    await deployment.start()
    runtime = deployment.runtime
    run_results = None
    test_output = ''

    try:
        if hasattr(runtime, '_config'):
            logger.info(f'Current RemoteRuntime timeout: {runtime._config.timeout}s')
            runtime._config.timeout = 1800.0
            logger.info(f'Overriding RemoteRuntime timeout to {runtime._config.timeout}s')

        # Issue a few one-off commands, similar to `subprocess.run()`
        logger.info(await runtime.execute(Command(command=['echo', 'Hello, world!'])))

        # Create a bash session
        await runtime.create_session(CreateBashSessionRequest())
        # The difference to one-off commands is that environment state persists.
        logger.info(await runtime.run_in_session(BashAction(command="export MYVAR='test'")))
        logger.info(await runtime.run_in_session(BashAction(command='echo $MYVAR')))

        # Forward host-side model endpoint credentials into the remote session.
        for key in (
            'ANTHROPIC_API_KEY',
            'OPENAI_API_KEY',
            'OPENAI_API_TYPE',
            'OPENAI_BASE_URL',
            'AZURE_API_KEY',
            'AZURE_OPENAI_API_KEY',
            'AZURE_API_BASE',
            'AZURE_API_VERSION',
        ):
            value = os.environ.get(key)
            if value:
                logger.info(await runtime.run_in_session(BashAction(command=f'export {key}={shlex.quote(value)}')))

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

        logger.info('Running runner script...')
        run_results = await runtime.run_in_session(
            BashAction(command=f'/agent/runner.sh "{model}" "{task}"', timeout=1200.0)
        )
        logger.info(f"agent's run results: {run_results}")
        logger.info('Runner script finished.')

        try:
            test_result = await runtime.run_in_session(BashAction(command=test_method))
            test_output = _extract_output(test_result)
            logger.info(test_output)
            score = _parse_score(test_output)
            return {
                'task': task,
                'project_path': project_path,
                'agent_run_results': run_results.output if hasattr(run_results, 'output') else str(run_results),
                'test_method': test_method,
                'test_output': test_output,
                'score': score,
                'status': 'success',
            }
        except Exception as e:
            logger.info(f'Error running test method: {e}')
            return {
                'task': task,
                'project_path': project_path,
                'agent_run_results': run_results.output if hasattr(run_results, 'output') else str(run_results),
                'test_method': test_method,
                'test_output': test_output,
                'score': 0,
                'status': f'error: {str(e)}',
            }
    finally:
        await deployment.stop()


def run_eval(deployment, project_path, task_id, task, model, agent_path, test_method, save_path):
    image = deployment or 'bastoica/ae-agent-ubuntu24.04:latest'

    config = DockerDeploymentConfig(
        image=image,
        startup_timeout=1200.0,
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
