import json
from collections import defaultdict


def aggregate_mr_test_by_algo_trace(jsonl_path):
    agg = defaultdict(list)

    with open(jsonl_path) as f:
        for line in f:
            data = json.loads(line)
            key = (data['algo'], data['trace_type'])
            mr_test = data.get('tuned_param_mr_info', {}).get('mr_test')
            if mr_test is not None:
                agg[key].append(mr_test)

    # 计算平均值
    result = defaultdict(dict)
    for (algo, trace_type), values in agg.items():
        avg = sum(values) / len(values)
        result[algo][trace_type] = avg

    return result


if __name__ == '__main__':
    path_to_file = 'llm_results_eval.jsonl'  # 替换为你的文件路径
    result = aggregate_mr_test_by_algo_trace(path_to_file)

    for algo in sorted(result):
        print(f'== {algo} ==')
        for trace_type, avg_mr_test in sorted(result[algo].items()):
            print(f'{algo} | {trace_type} -> avg mr_test: {avg_mr_test:.4f}')
        print()
