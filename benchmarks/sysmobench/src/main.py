"""SysMoBench integration for System Intelligence Benchmark Suite."""

import argparse
import json
import os
import sys
from datetime import datetime
from pathlib import Path

# Add paths
SDK_ROOT = Path(__file__).parent.parent.parent.parent
SYSMOBENCH_CORE = Path(__file__).parent.parent / "sysmobench_core"
SRC_ROOT = Path(__file__).parent
sys.path.insert(0, str(SDK_ROOT))
sys.path.insert(0, str(SYSMOBENCH_CORE))
sys.path.insert(0, str(SRC_ROOT))

# Import SDK
from sdk.utils import set_llm_endpoint_from_config  # noqa: E402
set_llm_endpoint_from_config(str(Path(__file__).parent.parent / 'env.toml'))

# Import SysMoBench
from tla_eval.tasks.loader import TaskLoader  # noqa: E402
from tla_eval.methods import get_method  # noqa: E402
from executor import SysMoExecutor  # noqa: E402
from evaluator import SysMoEvaluator  # noqa: E402

import logging
logging.basicConfig(level=logging.INFO, format='[%(levelname)s] %(message)s')
logger = logging.getLogger(__name__)


def main(input_file, output_dir, model_name, agent_name, max_iterations):
    """Main entry point."""
    # Change working directory to sysmobench_core so relative paths work correctly
    os.chdir(SYSMOBENCH_CORE)

    logger.info(f"SysMoBench | Model: {model_name} | Method: {agent_name} | Max iterations: {max_iterations}")

    # Initialize
    task_loader = TaskLoader(
        tasks_dir=str(SYSMOBENCH_CORE / "tla_eval" / "tasks"),
        cache_dir=str(SYSMOBENCH_CORE / "data" / "repositories")
    )
    method = get_method(agent_name)
    evaluator = SysMoEvaluator()
    executor = SysMoExecutor(method, model_name, evaluator, max_iterations)
    scores = []

    # Process tasks
    with open(input_file) as f, open(os.path.join(output_dir, 'result.jsonl'), 'w') as out:
        for line in f:
            item = json.loads(line)
            task_id, task_name = item['id'], item['task_name']
            logger.info(f"\n{'='*70}\nTask: {task_id} ({task_name})\n{'='*70}")

            try:
                task = task_loader.load_task(task_name)
                exec_result = executor.run(task)
                evaluation_outcome = exec_result.evaluation
                final_score = 1.0 if exec_result.success else SysMoEvaluator.final_score(evaluation_outcome)

                output = {
                    'id': task_id,
                    'task_name': task_name,
                    'model_name': model_name,
                    'success': exec_result.success,
                    'final_score': final_score,
                    'total_time': exec_result.total_time,
                    'iteration': exec_result.iteration or max_iterations
                }
                if exec_result.error:
                    output['error'] = exec_result.error

                scores.append(final_score)
            except Exception as e:
                logger.error(f"Error: {e}")
                output = {'id': task_id, 'error': str(e), 'final_score': 0.0}
                scores.append(0.0)

            out.write(json.dumps(output) + '\n')
            out.flush()

    # Save summary
    avg_score = {'final_score': sum(scores) / len(scores) if scores else 0.0, 'total_tasks': len(scores)}
    with open(os.path.join(output_dir, 'avg_score.json'), 'w') as f:
        json.dump(avg_score, f, indent=2)

    logger.info(f"\n{'='*70}\nFinal Score: {avg_score['final_score']:.3f}\n{'='*70}")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='SysMoBench Evaluation')
    parser.add_argument('-i', '--input_file', default='./data/benchmark/tasks.jsonl')
    parser.add_argument('-o', '--save_path', default=None)
    parser.add_argument('-a', '--agent', default='agent_based')
    parser.add_argument('-m', '--model_name', required=True)
    parser.add_argument('--max_iterations', type=int, default=3)
    args = parser.parse_args()

    # Output directory
    if not args.save_path:
        timestamp = datetime.now().strftime('%Y-%m-%d_%H-%M-%S')
        args.save_path = f"./outputs/sysmobench__{args.model_name.replace('/', '_')}__{args.agent}__{timestamp}"

    # Convert to absolute paths before changing working directory
    input_file = str(Path(args.input_file).resolve())
    save_path = str(Path(args.save_path).resolve())
    os.makedirs(save_path, exist_ok=True)

    main(input_file, save_path, args.model_name, args.agent, args.max_iterations)
