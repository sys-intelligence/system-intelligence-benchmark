import logging
import os

from cache_simulator.cache import CacheConfig
from cache_simulator.Simulator import SimulatorCache, SimulatorConfig


def simulate(policy_code=None, trace_path=None):
    import time

    if trace_path is None:
        trace_path = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            'cache',
            'trace',
            'zipf',
            'alpha1_m100_n1000',
            '0.oracleGeneral.bin',
        )

    simulator = SimulatorCache(
        SimulatorConfig(
            name='Cache',
            config=CacheConfig(
                capacity=9,
                consider_obj_size=False,
                trace_path=trace_path,
                key_col_id=1,
                size_col_id=2,
                has_header=False,
                delimiter=',',
            ),
            system_path=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cache'),
            tune_runs=20,
            code_folder=os.path.join(
                os.path.dirname(os.path.abspath(__file__)), 'log', 'qd_combine_optimizer_cache', 'code'
            ),
            tune_int_upper=None,
        )
    )

    if not policy_code:
        policy_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cache', 'sample_code', '214.py')
        with open(policy_path) as file:
            code = file.read()
    else:
        code = policy_code

    s = time.time()
    mr = simulator.simulate(
        code=code,
        code_id='any-id-you-like',
        need_log=False,
        check_code_exists=False,
        fix_default_param=False,
        need_save=False,
        need_copy_code=True,
        default_params=None,
    )
    e = time.time()
    logging.info(f'Simulate: time = {e-s}, mr = {mr}')
    print(f'Simulate: time = {e-s}, mr = {mr}')
    return e - s, mr


def tune():
    import time

    simulator = SimulatorCache(
        SimulatorConfig(
            name='Cache',
            config=CacheConfig(
                capacity=9,
                consider_obj_size=False,
                trace_path=os.path.join(
                    os.path.dirname(os.path.abspath(__file__)),
                    'cache',
                    'trace',
                    'zipf',
                    'alpha1_m100_n1000',
                    '0.oracleGeneral.bin',
                ),
                key_col_id=1,
                size_col_id=2,
                has_header=False,
                delimiter=',',
            ),
            system_path=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cache'),
            tune_runs=20,
            code_folder=os.path.join(
                os.path.dirname(os.path.abspath(__file__)), 'log', 'qd_combine_optimizer_cache', 'code'
            ),
            tune_int_upper=None,
        )
    )

    policy_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cache', 'sample_code', '214.py')

    with open(policy_path) as file:
        code = file.read()
        s = time.time()
        mr_info = simulator.tune(
            code=code,
            code_id='any-id-you-like',
            need_log=False,
            fixed_default_param=False,
            need_copy_code=True,
        )
        e = time.time()
        if mr_info != None:
            logging.info(
                f'Tune: time = {e-s}, tuned_mr = {mr_info[0]}, default_params = {mr_info[1]}, tuned_params = {mr_info[2]}'
            )
        else:
            logging.info(f'Tune: time = {e-s}, mr = None')


if __name__ == '__main__':
    tune()
    simulate()
