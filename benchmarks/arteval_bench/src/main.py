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

from run_eval_in_env import run_eval
from utils import get_task

def main(file_path, model, agent, save_path):
    """Main function for running the benchmark."""
    logger.info(f'Using model: {model}, agent: {agent}')
    with open(file_path) as f:
        for line in f:
            if not line.strip():
                continue  # Skip empty lines

            try:
                item = json.loads(line)
            except json.JSONDecodeError:
                logger.info(f'Skipping invalid JSON line: {line}')
                continue

            deployment = item.get('docker_env', None)
            project_path = f"./data/benchmark/{item.get('artifact_dir', None)}"
            task_file = item.get('artifact_readme', None)
            task_id = item.get('artifact_id', None)
            test_method = item.get('evaluator', None)

            task = get_task(task_file)

            result = run_eval(
                deployment=deployment,
                project_path=project_path,
                task_id=task_id,
                task=task,
                model=model,
                agent_path=agent,
                test_method=test_method,
                save_path=save_path,
            )
            with open(f'{save_path}/result.jsonl', 'a+', encoding='utf-8') as fw:
                fw.write(json.dumps(result) + '\n')

    success_count = 0
    total_count = 0
    with open(f'{save_path}/result.jsonl', encoding='utf-8') as f:
        for line in f:
            result = json.loads(line.strip())
            if result.get('status') == 'success':
                score_count += (result.get('score') == item.get('expected_score', -1))
            total_count += 1
    logger.info(f'Test run completed: {success_count}/{total_count} tasks succeeded.')
    summary_data = {'final_score': success_count / total_count, 'total_tasks': total_count}

    with open(os.path.join(save_path, 'avg_score.json'), 'w', encoding='utf-8') as summary_file:
        json.dump(summary_data, summary_file, indent=4)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='example benchmark')
    parser.add_argument(
        '-i',
        '--input_file',
        help='Benchmark input file',
        default='./data/benchmark/arteval_tasks.jsonl',
        #default='./data/benchmark/env_setup_examples.jsonl',
    )
    parser.add_argument('-o', '--save_path', help='Result save path', default=None)
    parser.add_argument(
        '-a',
        '--agent',
        help='Agent Name',
        default='claudecode',
    )
    parser.add_argument(
        '-m',
        '--model_name',
        help='Model Name',
        default='claude-sonnet-4-5-20250929',
    )
    # Note that if your benchmark has multiple tasks, you need to add --task <task>
    # in your code to enable task selection.
    parser.add_argument('-t', '--task', help='specify task in scenarios', default=None)

    args = parser.parse_args()

    model_name = args.model_name
    agent = args.agent
    input_file = args.input_file
    save_path = args.save_path
    task = args.task

    logger.debug(f"Benchmark path: {input_file}")

    if save_path is None:
        str_model_name = model_name.replace('/', '_')
        timestamp = datetime.now().strftime('%Y-%m-%d_%H-%M-%S')
        save_path = os.path.join('./outputs', f'env_setup_project__{str_model_name}__{args.agent}__{timestamp}')

    if agent == 'claudecode':
        agent = './src/agents/claudecode'
    save_path = os.path.abspath(os.path.expanduser(save_path))
    os.makedirs(save_path, exist_ok=True)

    main(input_file, model_name, agent, save_path)
