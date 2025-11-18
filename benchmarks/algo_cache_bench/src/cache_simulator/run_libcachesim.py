import logging
import os

from cache_simulator.utils import run_libcachesim


def eval_libcachesim(trace_path=None, cache_alg='tinyLFU'):
    if trace_path is None:
        raise ValueError("trace_path must be provided")
    if not os.path.exists(trace_path):
        raise FileNotFoundError(f"Trace file not found: {trace_path}")

    mr = run_libcachesim(
        cache_trace=trace_path,
        cache_alg=cache_alg,
        cache_cap=9,
        params='main-cache=clock,window-size=0.1',  # if you want to use default parameters, simply set params as "" (an emtpy string)
    )
    logging.info(f'Simulate: mr = {mr}')


if __name__ == '__main__':
    eval_libcachesim()
