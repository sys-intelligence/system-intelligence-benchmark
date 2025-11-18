import logging
import os

from utils import run_libcachesim, tune_libcachesim

if __name__ == '__main__':
    mr = run_libcachesim(
        cache_trace=os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            'cache',
            'trace',
            'zipf',
            'alpha1_m100_n1000',
            '0.oracleGeneral.bin',
        ),
        cache_alg='tinyLFU',
        cache_cap=9,
        params='main-cache=clock,window-size=0.1',  # if you want to use default parameters, simply set params as "" (an empty string)
    )
    logging.info(f'Simulate: mr = {mr}')

    mr_info = tune_libcachesim(
        trace=os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            'cache',
            'trace',
            'zipf',
            'alpha1_m100_n1000',
            '0.oracleGeneral.bin',
        ),
        alg='tinyLFU',
        cache_cap=9,
    )
    if mr_info != None:
        logging.info(
            f'Tune: default_mr = {mr_info[0]}, tuned_mr = {mr_info[1]}, default_params = {mr_info[2]}, tuned_params = {mr_info[3]}'
        )
    else:
        logging.info('Tune: mr = None')
