"""Example for benchmarking the performance of a model on a specific task."""

import argparse
import json
import os
import sys
from datetime import datetime

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../')))

from sdk.utils import set_llm_endpoint_from_config

set_llm_endpoint_from_config('env.toml')

from sdk.evaluator import BasicEvaluator  # noqa: E402
from sdk.executor import SimpleExecutor  # noqa: E402


def main(_input_file, output_dir, _model_name, agent_name):
    """Main function for running the benchmark."""
    total_score = []
    with (
        open(_input_file, encoding='utf-8') as data,
        open(os.path.join(output_dir, 'result.jsonl'), 'w', encoding='utf-8') as output_file,
    ):
        for line in data:
            item = json.loads(line)
            print('============ ' + item['id'] + ' ============')
            if agent_name == 'llm':
                executor = SimpleExecutor(_model_name, item['sys_prompt'])
            else:
                # You can add more agents here
                raise ValueError(f'Unknown agent name: {agent_name}')
            response = executor.run(item['user_prompt'])

            evaluator = BasicEvaluator(_model_name)
            offline_metrics = evaluator.eval(question=item['user_prompt'], answer=response, groundtruth=item)

            total_score.append(
                (
                    offline_metrics['syntax_acc'],
                    offline_metrics['exact_match'],
                    offline_metrics['jaccard_similarity'],
                    offline_metrics['cosine_similarity'],
                    offline_metrics['embeddings_similarity'],
                    offline_metrics['llmjudger_rating'],
                )
            )  # drop llmjudger_answer

            result = {
                'id': item['id'],
                'sys_prompt': item['sys_prompt'],
                'user_prompt': item['user_prompt'],
                'groundtruth': item['response'],
                'response': response,
                'syntax_acc': offline_metrics['syntax_acc'],
                'exact_match': offline_metrics['exact_match'],
                'jaccard_similarity': offline_metrics['jaccard_similarity'],
                'cosine_similarity': offline_metrics['cosine_similarity'],
                'embeddings_similarity': offline_metrics['embeddings_similarity'],
                'llmjudger_rating': offline_metrics['llmjudger_rating'],
                'llmjudger_answer': offline_metrics['llmjudger_answer'],
            }
            print('Evaluation Result:')
            print(result)
            output_file.write(json.dumps(result))
            output_file.write('\n')

    avg_score = [sum(values) / len(values) for values in list(zip(*total_score))]
    avg_score_dict = {
        'syntax_acc': avg_score[0],
        'exact_match': avg_score[1],
        'jaccard_similarity': avg_score[2],
        'cosine_similarity': avg_score[3],
        'embeddings_similarity': avg_score[4],
        'llmjudger_rating': avg_score[5],
        'final_score': sum(avg_score[:5]) / 5,  # Average of the first five metrics
    }
    with open(os.path.join(output_dir, 'avg_score.json'), 'w', encoding='utf-8') as avg_score_file:
        json.dump(avg_score_dict, avg_score_file, indent=4)
    print('************ Final average score ************')
    print(avg_score_dict)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='example benchmark')
    parser.add_argument(
        '-i',
        '--input_file',
        help='Benchmark input file',
        default='./data/benchmark/example_bench_benchmark_timestamp.jsonl',
    )
    parser.add_argument('-o', '--save_path', help='Result save path', default=None)
    # Add a parameter for agent
    parser.add_argument('-a', '--agent', help='Agent Name', default='llm')

    parser.add_argument(
        '-m',
        '--model_name',
        help='Model Name',
    )
    # Note that if your benchmark has multiple tasks, you need to add --task <task>
    # in your code to enable task selection.
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
