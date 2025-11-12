"""
Artifact Evaluation Benchmark

This script drives an agent to perform artifact evaluation,
namely succesfully setup, install, and run experiments 
for a series of software prototypes that accompany peer-reviewed
papers published at various CS conferences.

Author: Bogdan 'Bo' Stoica (bastoica@illinois.edu)
"""

import argparse
import json
import os
import sys
from datetime import datetime
from statistics import median
from statistics import mean
from loguru import logger

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../')))

from sdk.utils import set_llm_endpoint_from_config

set_llm_endpoint_from_config('env.toml')

from sdk.evaluator import Evaluator
from sdk.executor import Executor


ARTIFACT_STAGES = ("prep_environment", "build_code", "prep_benchmarks", "run_experiments")

class BasicExecutor(Executor):
    """Example class for one simple LLM module."""

    def __init__(self, _model_name, _sys_prompt) -> None:
        """Initialize the BasicExecutor class."""
        self.system_prompt = _sys_prompt
        self.model_name = _model_name
        self.LLM = LLM(engine=self.model_name, system_prompt=self.system_prompt, temperature=0.1)

    def run(self, nl, lang=''):
        """Run the model."""
        ans = self.LLM.query(nl)
        return ans


class ArtifactValidator(Evaluator):
    """Validation class for evaluating the model's ability to install, run, and test a given artifact."""

    def __init__(self) -> None:
        """Initialize the Evaluator class."""
        super().__init__()

    def run(cmd: Iterable[str]) -> Tuple[int, str, str]:
        """Run a command and return a (rc, stdout, stderr) tuple."""
        try:
            cp = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            return cp.returncode, cp.stdout or "", cp.stderr or ""
        except FileNotFoundError:
            return 127, "", ""

    def eval(self, cmd):
        """Run the artifact evaluation stage validator."""
        rc, stdout, stderr = self.run(cmd)
        if rc != 0:
            raise ValueError(f"Validation script failed with error code {rc}.")
        
        try:
            data = json.loads(stdout)
        except json.JSONDecodeError:
            return 0
        
        score_breakdown = {}
        for k in ARTIFACT_STAGES:
            if k not in data:
                raise KeyError(f"Missing required field: {k}")

            val = data[k]
            try:
                rc = int(val)
            except (TypeError, ValueError) as e:
                raise ValueError(f"Field '{k}' is not an integer error code: {val!r}") from e

            if not (0 <= rc <= 255):
                raise ValueError(f"Field '{k}' must be in range 0-255, got {rc}.")

            if rc == 0:
                success += 1
        
            score_breakdown[k] = 1 if rc == 0 else 0

        result = {
            "score_total": sum(score_breakdown.values()),
            "score_breakdown": score_breakdown,
        }
        return result



def main(input_file, output_dir, model_name, agent_name):
    """Main function for running the benchmark."""

    with open(input_file, encoding='utf-8') as f:
        data = [json.loads(line) for line in f]

    results = []
    for artifact in data:
        try:
            logger.info(f"============ {artifact['task_id']} ============")
            
            system_prompt = (
                f"You are an expert software engineer with experience with artifact evaluation tasks for computer science conferences.\n" 
                + f"You are asked to setup, install, and run experiments following instructions provided in the artifact's README.md file.\n"
            )

            task_file = artifact['task_file']
            with open(task_file, encoding='utf-8') as f:
                lines = f.readlines()
                task = "\n".join(lines)
            user_prompt = 'Below is the README of the artifact:\n\n' + task


            prompt = f"{system_prompt}\n {user_prompt}"
            if agent_name == 'llm':
                executor = BasicExecutor(model_name, prompt)
            else:
                raise ValueError(f'Unknown agent name: {agent_name}')
            
            response = executor.run(user_prompt, lang='json')
            response = json.loads(response)

            answer = str(response.get('answer', ''))
            explanation = response.get('explanation', '')
            logger.info(f'Model Answer: {answer}')
            logger.info(f'Model Explanation: {explanation}')

            test_method = artifact['test_method']

            evaluator = ArtifactValidator()
            metrics = evaluator.eval(cmd=test_method)

            result = {
                'id': artifact['instance_id'],
                'system_prompt': system_prompt,
                'user_prompt': user_prompt,
                'score_expected': artifact['expected_score'],
                'llm_answer': answer,
                'llm_explanation': explanation,
                'llm_score_final': metrics['score_total'],
                'llm_score_breakdown': metrics['score_breakdown'],
                'error': None,
            }
            results.append(result)

            logger.info('Evaluation Result:')
            logger.info(result)

        except Exception as e:
            logger.error(f"Error processing instance {artifact['task_id']}: {e}")
            result = {
                'id': artifact['instance_id'],
                'system_prompt': locals().get('system_prompt'),
                'user_prompt': locals().get('user_prompt'),
                'llm_answer': None,
                'llm_explanation': None,
                'llm_score_final': None,
                'llm_score_breakdown': None,
                'error': str(e),
            }
            results.append(result)

        with open(os.path.join(output_dir, 'result.jsonl'), 'a+', encoding='utf-8') as output_file:
            output_file.write(json.dumps(result))
            output_file.write('\n')

    scored = [
        r for r in results
        if r.get('error') in (None, '', 'null')  # only include successful artifact runs
        and isinstance(r.get('llm_score_final'), (int, float))
    ]

    overall_scores = [r['llm_score_final'] for r in scored]
    avg_overall = mean(overall_scores) if overall_scores else 0.0
    med_overall = median(overall_scores) if overall_scores else 0.0

    per_stage_values = {k: [] for k in ARTIFACT_STAGES}
    for r in scored:
        sb = r.get('llm_score_breakdown') or {}
        for k in ARTIFACT_STAGES:
            v = sb.get(k)
            if isinstance(v, (int)):
                per_stage_values[k].append(int(v))

    avg_by_stage = {
        k: (sum(vals) / len(vals)) if vals else 0.0
        for k, vals in per_stage_values.items()
    }

    med_by_stage = {
        k: (median(vals) if vals else 0.0)
        for k, vals in per_stage_values.items()
    }

    summary_data = {
        'artifact_count': len(scored),
        'average_overall_score': avg_overall,
        'median_overall_score': med_overall,
        'average_by_stage': avg_by_stage,
        'median_by_stage': med_by_stage,
    }

    with open(os.path.join(output_dir, 'avg_score.json'), 'w', encoding='utf-8') as summary_file:
        json.dump(summary_data, summary_file, indent=4)

    logger.info('************ Final average score ************')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='example benchmark')
    parser.add_argument(
        '-i',
        '--input_file',
        help='Benchmark input file',
        default='./data/benchmark/example_bench_benchmark_timestamp.jsonl',
    )
    parser.add_argument('-o', '--save_path', help='Result save path', default=None)
    parser.add_argument('-a', '--agent', help='Agent Name', default='llm')

    parser.add_argument(
        '-m',
        '--model_name',
        help='Model Name',
    )

    parser.add_argument('-t', '--task', help='specify task in scenarios', default=None)

    args = parser.parse_args()

    model_name = args.model_name
    input_file = args.input_file
    save_path = args.save_path

    if save_path is None:
        str_model_name = model_name.replace('/', '_')
        timestamp = datetime.now().strftime('%Y-%m-%d_%H-%M-%S')
        save_path = os.path.join('./outputs', f'examplebench__{str_model_name}__{args.agent}__{timestamp}')

    save_path = os.path.abspath(os.path.expanduser(save_path))
    os.makedirs(save_path, exist_ok=True)

    main(input_file, save_path, model_name, agent_name=args.agent)
