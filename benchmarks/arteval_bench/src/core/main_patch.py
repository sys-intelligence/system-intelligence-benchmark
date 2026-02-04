"""This script runs a benchmark for evaluating patches in a software project."""

import argparse
import json
import os
import sys
from datetime import datetime

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../')))

from sdk.logger import logger
from sdk.utils import set_llm_endpoint_from_config

set_llm_endpoint_from_config('env.toml')

from run_eval_sweagent import run  # noqa: E402


def main(file_path, save_path):
    """Main function for running the benchmark."""
    # file_path = "system_lab_tasks.jsonl"
    image = 'xuafeng/swe-go-python:latest'

    with open(file_path) as f:
        for line in f:
            if not line.strip():
                continue  # Skip empty lines

            try:
                task = json.loads(line)
            except json.JSONDecodeError:
                logger.info(f'Skipping invalid JSON line: {line}')
                continue

            task_id = task.get('task_id')
            repo_path = task.get('repo_name')
            problem_path = f'./data/benchmark/problems/{task_id}.md'
            test_method = task.get('test_method')

            run(task_id, repo_path, problem_path, test_method, image, save_path)

    success_count = 0
    total_count = 0
    with open(f'{save_path}/result.jsonl', encoding='utf-8') as f:
        for line in f:
            result = json.loads(line.strip())
            if result.get('status') == 'success':
                success_count += 1
            total_count += 1
    logger.info(f'Test run completed: {success_count}/{total_count} tasks succeeded.')
    summary_data = {'final_score': success_count / total_count, 'total_tasks': total_count}

    with open(os.path.join(save_path, 'avg_score.json'), 'w', encoding='utf-8') as summary_file:
        json.dump(summary_data, summary_file, indent=4)


def test_run():
    """Test function to run the benchmark with a sample task."""
    run(
        task_id='test_1',
        repo_path='projects/test-repo',
        problem_path='./data/benchmark/problems/test-repo-problems/1.md',
        test_method='pip install -e . && pytest tests/test_tribonaccy.py',
        image='xuafeng/swe-go-python:latest',
        save_path='./outputs/test_run',
    )

    success_count = 0
    total_count = 0
    with open('./outputs/test_run/result.jsonl', encoding='utf-8') as f:
        for line in f:
            result = json.loads(line.strip())
            if result.get('status') == 'success':
                success_count += 1
            total_count += 1
    logger.info(f'Test run completed: {success_count}/{total_count} tasks succeeded.')
    summary_data = {'score': success_count / total_count, 'total_tasks': total_count}

    with open('./outputs/test_run/avg_score.json', 'w', encoding='utf-8') as summary_file:
        json.dump(summary_data, summary_file, indent=4)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='example benchmark')
    parser.add_argument(
        '-i',
        '--input_file',
        help='Benchmark input file',
        # default='./data/benchmark/system_lab_tasks.jsonl',
        default='./data/benchmark/system_lab_tasks.jsonl',
    )
    parser.add_argument('-o', '--save_path', help='Result save path', default=None)
    parser.add_argument('-a', '--agent', help='Agent Name', default='sweagent')
    parser.add_argument(
        '-m',
        '--model_name',
        help='Model Name',
        default='gpt-4o',
    )
    # Note that if your benchmark has multiple tasks, you need to add --task <task>
    # in your code to enable task selection.
    parser.add_argument('-t', '--task', help='specify task in scenarios', default=None)

    args = parser.parse_args()

    model_name = args.model_name
    input_file = args.input_file
    save_path = args.save_path
    task = args.task
    if task == 'test':
        logger.info('Running test benchmark...')
        test_run()
    else:
        if save_path is None:
            str_model_name = model_name.replace('/', '_')
            timestamp = datetime.now().strftime('%Y-%m-%d_%H-%M-%S')
            save_path = os.path.join('./outputs', f'systemcourseproject__{str_model_name}__{args.agent}__{timestamp}')

        save_path = os.path.abspath(os.path.expanduser(save_path))
        os.makedirs(save_path, exist_ok=True)

        main(input_file, save_path)
