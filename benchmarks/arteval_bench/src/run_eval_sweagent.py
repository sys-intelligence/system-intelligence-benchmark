import sys
import subprocess

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../')))

from patch_evaluator import pacth_eval

from sdk.logger import logger


def run(task_id, repo_path, problem_path, test_method, image, save_path):
    """Run the benchmark for a specific task."""
    output_dir = f'{save_path}/patch/{task_id}'
    patch_file = os.path.join(output_dir, '1c2844', '1c2844.patch')

    # Use sweagent to generate a patch for the task
    command = [
        'sweagent',
        'run',
        '--config',
        './src/config_aoi.yaml',
        '--env.repo.path',
        './data/benchmark/' + repo_path,
        '--problem_statement.path',
        problem_path,
        '--output_dir',
        output_dir,
        '--env.deployment.image',
        image,
        '--env.post_startup_commands',
        '["export PATH=/usr/local/go/bin:${PATH} && export HOME=/tmp"]',
    ]

    logger.info('Executing sweagent command...')
    subprocess.run(command, check=True, timeout=600)

    logger.info('\n\n==========================')
    logger.info(f'Patch file expected at: {patch_file}')

    # Evaluate the generated patch
    eval_out = pacth_eval(
        task_id=task_id,
        project_path=repo_path,
        patch=patch_file,
        test_method=test_method,
        output_path=output_dir,
        image=image,
    )
    logger.info('Patch evaluation completed.')

    with open(f'{save_path}/result.jsonl', 'a+', encoding='utf-8') as fw:
        fw.write(json.dumps(eval_out) + '\n')
    logger.info('Evaluation completed successfully.')
