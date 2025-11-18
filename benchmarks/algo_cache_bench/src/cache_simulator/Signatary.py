import os
import time
from multiprocessing import Pool
from typing import List

import numpy as np
from cache import CacheConfig, Trace
from Simulator import SimulatorCache, SimulatorConfig
from utils import run_libcachesim, tune_libcachesim


def signatary_simulate(simulator: SimulatorCache):
    return simulator.simulate(
        code='',
        code_id='signature',
        need_log=False,
        check_code_exists=False,
        fix_default_param=False,
        need_save=False,
        need_copy_code=False,
    )


class Signatary:
    def __init__(self, test_folder, is_admission=False, trace_filter=None):
        if trace_filter == None:
            test_trace_list = sorted(os.listdir(test_folder))
        else:
            test_trace_list = [t for t in sorted(os.listdir(test_folder)) if trace_filter(t) == False]
        test_trace_cap_list = []
        for test_trace_file in test_trace_list:
            trace = Trace(trace_path=os.path.join(test_folder, test_trace_file), next_vtime_set=True)
            cap = int(trace.get_ndv() * 0.1)
            if cap < 1:
                cap = 1
            test_trace_cap_list.append(cap)

        self.test_simulator_list = [
            SimulatorCache(
                SimulatorConfig(
                    name='Cache',
                    config=CacheConfig(
                        capacity=test_trace_cap,
                        consider_obj_size=False,
                        trace_path=os.path.join(test_folder, test_trace_file),
                        key_col_id=1,
                        size_col_id=2,
                        has_header=False,
                        delimiter=',',
                    ),
                    system_path=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cache'),
                    tune_runs=1,
                    code_folder=os.path.join(
                        os.path.dirname(os.path.abspath(__file__)), 'log', 'qd_combine_optimizer_cache', 'code'
                    ),
                    tune_int_upper=None,
                )
            )
            for (test_trace_file, test_trace_cap) in zip(test_trace_list, test_trace_cap_list)
        ]
        self.is_admission = is_admission
        if is_admission == False:
            self.belady = [
                run_libcachesim(
                    cache_trace=sim.config.trace_path,
                    cache_alg='belady',
                    cache_cap=sim.config.capacity,
                )
                for sim in self.test_simulator_list
            ]
        else:
            self.belady = [0.0 for _ in self.test_simulator_list]
        assert all([b != None for b in self.belady])
        self.latency = 0.0

    @property
    def dimension(self):
        return len(self.belady)

    def _normalize_miss_ratio(self, mr: float, belady_mr: float):
        if mr == None:
            return None
        if belady_mr == 1.0:
            return 0.0
        return round(np.clip((mr - belady_mr) / (1.0 - belady_mr), 0.0, 1.0), 4)

    def _normalize_signature(self, raw_signature: List[float]):
        return [self._normalize_miss_ratio(mr, belady_mr) for (mr, belady_mr) in zip(raw_signature, self.belady)]

    def sign(self, code: str, is_sota: bool = False):
        if is_sota == True:
            if self.is_admission == True:
                alg = 'fifo'
                admission_alg = code
            else:
                alg = code
                admission_alg = ''
            signature = []
            start = time.time()
            for sim in self.test_simulator_list:
                mr_info = tune_libcachesim(
                    trace=sim.config.trace_path,
                    alg=alg,
                    cache_cap=sim.config.capacity,
                    fixed_default_params=True,
                    tune_runs=1,
                )
                assert mr_info != None
                mr = mr_info[1]
                assert mr != None
                signature.append(mr)
            end = time.time()
            self.latency += end - start
            return self._normalize_signature(signature)

        # is_sota = False
        example_sim = self.test_simulator_list[0]
        copy_dest = os.path.join(example_sim.system_path, 'My.py')
        assert os.path.exists(copy_dest)
        with open(copy_dest, 'w') as file:
            file.write(example_sim._fix_default_param_for_code(code))
        signature = []
        start = time.time()
        with Pool(len(self.test_simulator_list) * 2) as p:
            signature = p.map(signatary_simulate, self.test_simulator_list)
        end = time.time()
        self.latency += end - start
        return self._normalize_signature(signature)

    def to_dict(self):
        return {'simulators': [sim.to_dict() for sim in self.test_simulator_list], 'latency': self.latency}
