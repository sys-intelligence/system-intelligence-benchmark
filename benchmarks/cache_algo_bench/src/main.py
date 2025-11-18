"""Example for benchmarking the performance of a model on a specific task."""

import argparse
import json
import os
import sys
from datetime import datetime

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../')))


from sdk.utils import set_llm_endpoint_from_config

set_llm_endpoint_from_config('env.toml')

from cache_simulator.run_simulatorcache import simulate  # noqa: E402

from sdk.evaluator import Evaluator  # noqa: E402
from sdk.executor import SimpleExecutor  # noqa: E402


class CacheSimulator(Evaluator):
    """Evaluator class for evaluating the performance of the model."""

    def __init__(self) -> None:
        """Initialize the Evaluator class."""
        super().__init__()

    def list_all_files(self, folder_path):
        """List all files in the given folder and its subfolders."""
        file_paths = []
        for root, _, files in os.walk(folder_path):
            for file in files:
                full_path = os.path.join(root, file)
                file_paths.append(full_path)
        return file_paths

    def eval(self, response, trace_path):
        """Run the cache simulation on all traces in the specified path."""
        all_traces = self.list_all_files(trace_path)
        print('all_traces:', all_traces)

        all_time_cost = []
        all_miss_rate = []
        for trace in all_traces:
            time_cost, miss_rate = simulate(response, trace_path=trace)
            all_time_cost.append(time_cost)
            all_miss_rate.append(miss_rate)

        time_cost = sum(all_time_cost) / len(all_time_cost)
        miss_rate = sum(all_miss_rate) / len(all_miss_rate)
        return {'time_cost': time_cost, 'miss_rate': miss_rate}


def main(_input_file, output_dir, _model_name, trace_path=None):
    """Main function for running the benchmark."""
    total_score = []
    with (
        open(_input_file, encoding='utf-8') as data,
        open(os.path.join(output_dir, 'result.jsonl'), 'w', encoding='utf-8') as output_file,
    ):
        for line in data:
            item = json.loads(line)
            print('============ ' + item['id'] + ' ============')

            # TODO: extract the following to a MultiRoundExecutor class
            executor = SimpleExecutor(_model_name, item['sys_prompt'])
            response = executor.run(item['user_prompt'], lang='python')
            print('Response from model:')
            print(response)

            evaluator = CacheSimulator()
            all_round_results = []
            for round in range(3):
                print(f'Round {round + 1} of evaluation...')
                # Simulate the cache algorithm
                print('Simulating cache algorithm...')

                eval_result = evaluator.eval(response, trace_path=trace_path)
                if not eval_result['miss_rate']:
                    print('Simulation failed, please refine your response.')
                    continue
                print(f'Time Cost: {eval_result["time_cost"]:.6f} seconds')
                print(f'Miss Rate: {eval_result["miss_rate"]:.6f}')

                all_round_results.append((eval_result['time_cost'], eval_result['miss_rate']))

                refine_prompt = f"""
                The cache algorithm has been simulated with the following results:
                - Average Time Cost: {eval_result["time_cost"]:.6f} seconds
                - Average Miss Rate: {eval_result["miss_rate"]:.6f}
                Please refine your policy based on these results to reduce the miss_rate.
                """
                response = executor.run(refine_prompt, lang='python')

            print('Final Response after refinement:')
            eval_result = evaluator.eval(response, trace_path=trace_path)
            all_round_results.append((eval_result['time_cost'], eval_result['miss_rate']))
            print(f'Final Time Cost: {eval_result["time_cost"]:.6f} seconds')
            print(f'Final Miss Rate: {eval_result["miss_rate"]:.6f}')

            print('All rounds results:')
            for idx, (time_cost, miss_rate) in enumerate(all_round_results):
                print(f'Round {idx + 1}: Time Cost = {time_cost:.6f} seconds, Miss Rate = {miss_rate:.6f}')
            # evaluator = Evaluator(_model_name)
            # offline_metrics = evaluator.offline_evaluate(question=item['user_prompt'], query=response, groundtruth=item)

            total_score.append([miss_rate, time_cost])  # drop llmjudger_answer
            result = {
                'id': item['id'],
                'sys_prompt': item['sys_prompt'],
                'user_prompt': item['user_prompt'],
                'response': response,
                'miss_rate': miss_rate,
                'time_cost': time_cost,
            }
            print('Evaluation Result:')
            print(result)
            output_file.write(json.dumps(result))
            output_file.write('\n')

    avg_score = [sum(values) / len(values) for values in list(zip(*total_score))]
    avg_score_dict = {'miss_rate': avg_score[0], 'time_cost': avg_score[1], 'final_score': avg_score[0]}
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
        default='./data/benchmark/cache_benchmarks.jsonl',
    )
    parser.add_argument('-o', '--save_path', help='Result save path', default=None)
    parser.add_argument('-a', '--agent', help='Agent Name', default='llm')
    parser.add_argument(
        '-m',
        '--model_name',
        help='Model Name',
    )
    # Note that if your benchmark has multiple tasks, you need to add --task <task>
    # in your code to enable task selection.
    parser.add_argument(
        '-t',
        '--task',
        help='specify task in scenarios',
        choices=['alibaba-storage', 'ra-fwe', 'ra-multikey', 'tencentblock-storage', 'tmp', 'zipf'],
        default='tmp',
    )

    args = parser.parse_args()

    model_name = args.model_name
    print('Using model:', model_name)
    input_file = args.input_file
    save_path = args.save_path

    trace_path = f'./data/benchmark/trace/{args.task}' if args.task else None

    if save_path is None:
        str_model_name = model_name.replace('/', '_')
        timestamp = datetime.now().strftime('%Y-%m-%d_%H-%M-%S')
        save_path = os.path.join('./outputs', f'cachebench__{str_model_name}__{args.agent}__{args.task}__{timestamp}')

    save_path = os.path.abspath(os.path.expanduser(save_path))
    os.makedirs(save_path, exist_ok=True)

    main(input_file, save_path, model_name, trace_path=trace_path)
