"""Patch evaluator for running tests in a deployment."""

import asyncio
import json
import os

from swerex.deployment.docker import DockerDeployment
from swerex.runtime.abstract import BashAction, Command, CreateBashSessionRequest, UploadRequest

from sdk.logger import logger


async def run_some_stuff(task_id, project_path, patch, test_method, deployment):
    """Spoiler: This function will work with any deployment."""
    await deployment.start()
    runtime = deployment.runtime

    # Issue a few one-off commands, similar to `subprocess.run()`
    logger.info(await runtime.execute(Command(command=['echo', 'Hello, world!'])))

    # Create a bash session
    await runtime.create_session(CreateBashSessionRequest())

    # Run a command in the session
    # The difference to the one-off commands is that environment state persists!
    logger.info(await runtime.run_in_session(BashAction(command="export MYVAR='test'")))
    logger.info(await runtime.run_in_session(BashAction(command='echo $MYVAR')))

    logger.info(
        await runtime.upload(
            UploadRequest(
                source_path='./data/benchmark/projects',
                target_path='/projects',
            )
        )
    )
    logger.info(
        await runtime.upload(
            UploadRequest(
                source_path=patch,
                target_path='/patch.patch',
            )
        )
    )

    logger.info(await runtime.run_in_session(BashAction(command='export PATH=/usr/local/go/bin:${PATH}')))
    logger.info(await runtime.run_in_session(BashAction(command='export HOME=/tmp')))
    logger.info(await runtime.run_in_session(BashAction(command='go version')))
    logger.info(await runtime.run_in_session(BashAction(command='pip install pytest')))
    # logger.info(await runtime.run_in_session(BashAction(command="pytest -v")))

    logger.info(await runtime.run_in_session(BashAction(command='ls /projects')))
    logger.info(await runtime.run_in_session(BashAction(command='ls /patch.patch')))

    logger.info(await runtime.run_in_session(BashAction(command='cd /' + project_path)))
    logger.info(await runtime.run_in_session(BashAction(command='git apply /patch.patch')))
    logger.info(await runtime.run_in_session(BashAction(command='pwd')))

    try:
        test_output = await runtime.run_in_session(BashAction(command=test_method))
        logger.info(test_output)
        return {
            'task_id': task_id,
            'reop_location': project_path,
            'patch': patch,
            'test_method': test_method,
            'status': 'success',
            'output': test_output.output if hasattr(test_output, 'output') else str(test_output),
        }
    except Exception as e:
        logger.info(f'Error running test method: {e}')
        return {
            'task_id': task_id,
            'reop_location': project_path,
            'patch': patch,
            'test_method': test_method,
            'status': 'error',
            'output': str(e),
        }

    # logger.info(await runtime.run_in_session(BashAction(command="cd projects/6.5840-golabs-2024/src/kvsrv")))
    # logger.info(await runtime.run_in_session(BashAction(command="go test")))

    await deployment.stop()


def pacth_eval(task_id, project_path, patch, test_method, output_path, image):
    """Evaluate a patch by running a test method in a deployment."""
    # deployment = LocalDeployment()
    deployment = DockerDeployment(image=image)
    if not os.path.exists(patch):
        logger.error(f'Patch file {patch} does not exist.')
        eval_out = {
            'task_id': task_id,
            'reop_location': project_path,
            'patch': '',
            'test_method': test_method,
            'status': 'no_patch',
            'output': 'Patch file does not exist.',
        }

    else:
        eval_out = asyncio.run(run_some_stuff(task_id, project_path, patch, test_method, deployment))

    return eval_out


if __name__ == '__main__':
    # add arguments via argparse
    import argparse

    parser = argparse.ArgumentParser(description='Run some stuff in a deployment.')
    parser.add_argument('--task_id', type=str, required=True, help='Task ID')
    parser.add_argument('--project_path', type=str, required=True, help='Project path')
    parser.add_argument('--patch', type=str, required=True, help='Patch file path')
    parser.add_argument('--test_method', type=str, required=True, help='Test method command')
    parser.add_argument('--output_path', type=str, default='eval_results', help='Output file path')
    parser.add_argument('--image', type=str, default='xuafeng/swe-go-python:latest', help='Deployment type')

    # Parse the arguments
    args = parser.parse_args()
    task_id = args.task_id
    project_path = args.project_path
    patch = args.patch
    test_method = args.test_method
    output_path = args.output_path
    image = args.image

    eval_out = pacth_eval(task_id, project_path, patch, test_method, output_path, image)

    with open(os.path.join(output_path, f'{task_id}_result.json'), 'w', encoding='utf-8') as fw:
        fw.write(json.dumps(eval_out, indent=4))
    logger.info('Evaluation completed successfully.')
