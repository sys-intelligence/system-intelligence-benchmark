import os

from Analyzer import Analyzer
from CrossValidator import CrossValidator


def get_traces():
    trace_folder = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), 'cache', 'trace', 'zipf', 'alpha1_m100_n1000'
    )
    trace_file_list = sorted([f for f in os.listdir(trace_folder)])
    trace_path_list = [os.path.join(trace_folder, f) for f in trace_file_list]
    return trace_path_list


def test(
    is_sota: bool,  # whether the policy is your self-designed policy or an exsting SOTA policy in libcachesim
    policy: str,  # absolute path to the code of your policy, or the name of a SOTA policy in libcachesim
):
    analyzer = Analyzer()
    trace_path_list = get_traces()
    for trace_path in trace_path_list:
        analyzer.simulate(trace_path=trace_path, cache_cap_frac=0.1, algo=policy, is_sota=is_sota)
        # the result will be written to analysis/miss_ratio.jsonl
    # After getting the tuned parameters of every trace, simulate each parameter on other traces.
    cross_validator = CrossValidator()
    cross_validator.simulate(
        algo=policy,
        is_sota=is_sota,
        trace_path_list=trace_path_list,
        cache_cap_frac=0.1,
    )


def plot(
    algo_list: list,
):
    def trace_filter(trace_path):
        """Select the traces you want. Here simply select all traces under the trace_folder."""
        return True

    Analyzer().plot_miss_ratio_percentile(
        trace_filter=trace_filter,
        algo_list=algo_list,
        cache_cap_frac=0.1,
        png_path=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'analysis', 'miss_ratio_percentile.png'),
        use_default=False,  # whether to use the tuned miss ratio or the default miss ratio for each algo.
    )
    CrossValidator().plot_miss_ratio_percentile(
        trace_filter=trace_filter,
        algo_list=algo_list,
        cache_cap_frac=0.1,
        png_path=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'analysis', 'xval_miss_ratio_percentile.png'),
    )


if __name__ == '__main__':
    sota_algo_list = ['fifo', 'lfu', 'random', 'lru', 'slru', 'arc', 'clock', 'sieve', 's3fifo', 'tinyLFU', 'belady']
    self_designed_algo_list = [
        os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cache', 'sample_code', '214.py')
    ]
    for algo in sota_algo_list + self_designed_algo_list:
        if algo in sota_algo_list:
            test(True, algo)
        else:
            test(False, algo)
    plot(sota_algo_list + self_designed_algo_list)
