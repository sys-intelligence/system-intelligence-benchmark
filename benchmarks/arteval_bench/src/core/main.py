"""This script runs a benchmark for evaluating patches in a software project."""

import argparse
import json
import os
from datetime import datetime
from pathlib import Path

from sdk.logger import logger
from sdk.utils import set_llm_endpoint_from_config

set_llm_endpoint_from_config(str(Path(__file__).resolve().parents[2] / 'env.toml'))

from run_eval_in_env import run_eval
from utils import get_task

BENCH_ROOT = Path(__file__).resolve().parents[2]


def _resolve_agent_path(agent_name_or_path: str) -> str:
    built_in_agents = {
        'claudecode': BENCH_ROOT / 'src' / 'core' / 'agents' / 'claudecode',
        'openhand': BENCH_ROOT / 'src' / 'core' / 'agents' / 'openhand',
        'minisweagent': BENCH_ROOT / 'src' / 'core' / 'agents' / 'minisweagent',
    }
    if agent_name_or_path in built_in_agents:
        return str(built_in_agents[agent_name_or_path])
    return str(Path(agent_name_or_path).expanduser().resolve())


def _normalize_task_file_for_uploaded_repo(artifact_dir: str, task_file: str) -> str:
    # Uploaded folder is mounted as /repo, so remove duplicated leading artifact dir when present.
    prefix = f'{artifact_dir}/'
    if task_file.startswith(prefix):
        return task_file[len(prefix) :]
    return task_file


def main(file_path, model, agent, save_path, task_filter=None):
    """Main function for running the benchmark."""
    logger.info(f'Using model: {model}, agent: {agent}')
    results = []
    result_file = Path(save_path) / 'result.jsonl'

    with open(file_path) as f:
        for line in f:
            if not line.strip():
                continue  # Skip empty lines

            try:
                item = json.loads(line)
            except json.JSONDecodeError:
                logger.info(f'Skipping invalid JSON line: {line}')
                continue

            task_id = item.get('artifact_id')
            if task_filter and task_id != task_filter:
                continue

            artifact_dir = item.get('artifact_dir')
            if not artifact_dir:
                logger.info('Skipping entry without artifact_dir: %s', item)
                continue

            task_file = item.get('artifact_readme')
            if not task_file:
                logger.info('Skipping entry without artifact_readme: %s', item)
                continue

            deployment = item.get('docker_env') or item.get('docer_env')
            expected_score = item.get('expected_score')
            project_path = str((BENCH_ROOT / 'data' / 'benchmark' / artifact_dir).resolve())
            test_method = item.get('evaluator')
            normalized_task_file = _normalize_task_file_for_uploaded_repo(artifact_dir, task_file)

            task = get_task(normalized_task_file)

            logger.info('Running task_id=%s project_path=%s', task_id, project_path)

            try:
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
            except Exception as e:
                logger.exception('Task %s failed during evaluation', task_id)
                result = {
                    'task_id': task_id,
                    'project_path': project_path,
                    'test_method': test_method,
                    'score': 0,
                    'status': f'error: {str(e)}',
                }

            result['artifact_id'] = task_id
            result['expected_score'] = expected_score
            results.append(result)
            with open(result_file, 'a+', encoding='utf-8') as fw:
                fw.write(json.dumps(result) + '\n')

    success_count = 0
    matched_expected_count = 0
    total_count = len(results)
    for result in results:
        if result.get('status') == 'success':
            success_count += 1
            expected = result.get('expected_score')
            if expected is not None and result.get('score') == expected:
                matched_expected_count += 1

    logger.info(f'Test run completed: {success_count}/{total_count} tasks succeeded.')
    summary_data = {
        'final_score': (matched_expected_count / total_count) if total_count else 0.0,
        'success_rate': (success_count / total_count) if total_count else 0.0,
        'total_tasks': total_count,
        'succeeded_tasks': success_count,
        'matched_expected_score_tasks': matched_expected_count,
    }

    with open(os.path.join(save_path, 'avg_score.json'), 'w', encoding='utf-8') as summary_file:
        json.dump(summary_data, summary_file, indent=4)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='arteval benchmark')
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
    agent = _resolve_agent_path(args.agent)
    input_file = args.input_file
    save_path = args.save_path
    task = args.task

    logger.debug(f"Benchmark path: {input_file}")

    if save_path is None:
        str_model_name = model_name.replace('/', '_')
        timestamp = datetime.now().strftime('%Y-%m-%d_%H-%M-%S')
        save_path = os.path.join('./outputs', f'env_setup_project__{str_model_name}__{args.agent}__{timestamp}')

    if not Path(agent).exists():
        raise FileNotFoundError(f'Agent path does not exist: {agent}')

    save_path = os.path.abspath(os.path.expanduser(save_path))
    os.makedirs(save_path, exist_ok=True)

    main(input_file, model_name, agent, save_path, task_filter=task)
