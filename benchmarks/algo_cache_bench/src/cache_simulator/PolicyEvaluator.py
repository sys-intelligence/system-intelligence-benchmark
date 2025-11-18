import json
import logging
import os
from typing import Dict, List

from cache import CacheConfig, Trace
from Simulator import SimulatorCache, SimulatorConfig
from utils import miss_ratio_reduction, plot_mr, run_libcachesim, tune_libcachesim, write_to_file


class MissRatioInfo:
    def __init__(self, params: Dict, mr_train: float, mr_test: float):
        self.params = params
        self.mr_train = mr_train
        self.mr_test = mr_test

    def to_dict(self):
        return {'params': self.params, 'mr_train': self.mr_train, 'mr_test': self.mr_test}


class Entry:
    def __init__(
        self,
        trace_type: str,
        trace_file_name: str,
        train_frac: int,
        cache_cap: int,
        cache_cap_frac: float,
        algo: str,
        is_sota: bool,
        init_param_mr_info: MissRatioInfo,
        tuned_param_mr_info: MissRatioInfo,
    ):
        self.trace_type = trace_type
        self.trace_file_name = trace_file_name
        self.train_frac = train_frac  # 10-base frac, thus this is an integer
        self.cache_cap = cache_cap
        self.cache_cap_frac = cache_cap_frac
        self.algo = algo
        self.is_sota = is_sota
        self.init_param_mr_info = init_param_mr_info
        self.tuned_param_mr_info = tuned_param_mr_info

    def __str__(self):
        return f'({self.algo}, {self.trace_type}, {self.trace_file_name}, train={self.train_frac}, ccf={self.cache_cap_frac})'

    def __repr__(self):
        return f'({self.algo}, {self.trace_type}, {self.trace_file_name}, train={self.train_frac}, ccf={self.cache_cap_frac})'

    @classmethod
    def from_dict(cls, trace_analysis_entry_dict):
        return Entry(
            trace_type=trace_analysis_entry_dict['trace_type'],
            trace_file_name=trace_analysis_entry_dict['trace_file_name'],
            train_frac=trace_analysis_entry_dict['train_frac'],
            cache_cap=trace_analysis_entry_dict['cache_cap'],
            cache_cap_frac=trace_analysis_entry_dict['cache_cap_frac'],
            algo=trace_analysis_entry_dict['algo'],
            is_sota=trace_analysis_entry_dict['is_sota'],
            init_param_mr_info=MissRatioInfo(
                params=trace_analysis_entry_dict['init_param_mr_info']['params'],
                mr_train=trace_analysis_entry_dict['init_param_mr_info']['mr_train'],
                mr_test=trace_analysis_entry_dict['init_param_mr_info']['mr_test'],
            ),
            tuned_param_mr_info=MissRatioInfo(
                params=trace_analysis_entry_dict['tuned_param_mr_info']['params'],
                mr_train=trace_analysis_entry_dict['tuned_param_mr_info']['mr_train'],
                mr_test=trace_analysis_entry_dict['tuned_param_mr_info']['mr_test'],
            ),
        )

    @classmethod
    def from_jsonl(cls, jsonl: str):
        trace_analysis_entry_dict = json.loads(jsonl)
        return Entry.from_dict(trace_analysis_entry_dict)

    def to_dict(self):
        trace_analysis_entry_dict = {
            'algo': self.algo,
            'trace_type': self.trace_type,
            'trace_file_name': self.trace_file_name,
            'cache_cap_frac': self.cache_cap_frac,
            'train_frac': self.train_frac,
            'cache_cap': self.cache_cap,
            'is_sota': self.is_sota,
            'init_param_mr_info': self.init_param_mr_info.to_dict(),
            'tuned_param_mr_info': self.tuned_param_mr_info.to_dict(),
        }
        return trace_analysis_entry_dict

    def to_jsonl(self):
        return json.dumps(self.to_dict())


class PolicyEvaluator:
    trace_root_folder = '/home/v-ruiyingma/llm4sys/cache/trace'
    trace_analysis_folder = '/home/v-ruiyingma/cacheProj/analysis'
    policy_eval_jsonl_path = os.path.join(trace_analysis_folder, 'policy_eval.jsonl')

    def __init__(self):
        with open(self.policy_eval_jsonl_path) as file:
            file_lines = file.readlines()
        self.entries = [Entry.from_jsonl(l) for l in file_lines]

    def _get_trace_path(self, trace_type, trace_file_name, train_frac: int, is_train: bool):
        # full trace
        if is_train == None:
            if trace_type == 'fwe' or trace_type == 'multikey':
                trace_path = os.path.join(self.trace_root_folder, 'real', 'llm_trace', trace_file_name)
                assert trace_type in trace_path
                assert trace_file_name in trace_file_name
            elif trace_type == 'alibaba1k' or trace_type == 'alibaba10k' or trace_type == 'tencentblock1k':
                trace_path = os.path.join(self.trace_root_folder, 'real', trace_type, trace_file_name)
            else:
                raise ValueError(f'Unknown trace type: {trace_type}')
        else:
            assert isinstance(is_train, bool)
            # test-train
            test_frac = 10 - train_frac
            test_train_folder = 'train' if is_train == True else 'test'
            if trace_type == 'fwe' or trace_type == 'multikey':
                trace_path = os.path.join(
                    self.trace_root_folder,
                    'real',
                    f'llm_trace_{train_frac}_{test_frac}',
                    test_train_folder,
                    trace_file_name,
                )
                assert trace_type in trace_path
                assert trace_file_name in trace_file_name
            elif trace_type == 'alibaba1k' or trace_type == 'alibaba10k' or trace_type == 'tencentblock1k':
                trace_path = os.path.join(
                    self.trace_root_folder,
                    'real',
                    f'{trace_type}_{train_frac}_{test_frac}',
                    test_train_folder,
                    trace_file_name,
                )
                assert trace_type in trace_path
                assert trace_file_name in trace_file_name
            else:
                raise ValueError(f'Unknown trace type: {trace_type}')
        assert os.path.exists(trace_path)
        return trace_path

    def _get_simulator(self, trace_path, cache_cap):
        return SimulatorCache(
            SimulatorConfig(
                name='Cache',
                config=CacheConfig(
                    capacity=cache_cap,
                    consider_obj_size=False,
                    trace_path=trace_path,
                    key_col_id=1,
                    size_col_id=2,
                    has_header=False,
                    delimiter=',',
                ),
                system_path=os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cache'),
                tune_runs=20,
                code_folder=os.path.join(self.trace_analysis_folder, 'log', 'qd_combine_optimizer_cache', 'code'),
                tune_int_upper=None,
            )
        )

    def _tune_sota(self, algo, trace_path, cache_cap):
        miss_ratio_info_tuple = tune_libcachesim(trace=trace_path, alg=algo, cache_cap=cache_cap)
        assert miss_ratio_info_tuple != None
        return miss_ratio_info_tuple

    def _tune_not_sota(self, algo, trace_path, cache_cap):
        simulator = self._get_simulator(trace_path, cache_cap)
        code_path = algo
        code_id = algo
        with open(code_path) as file:
            code = file.read()
        default_mr = simulator.simulate(
            code=code,
            code_id='tune_not_sota',
            need_log=True,
            check_code_exists=False,
            fix_default_param=False,
            need_save=False,
        )
        assert default_mr != None
        tuned_mr, default_params, tuned_params = simulator.tune(
            code=code, code_id=code_id, fixed_default_param=False, need_log=True
        )
        if tuned_mr == None or tuned_mr > default_mr:
            tuned_mr = default_mr
            tuned_params = default_params

        return tuple([default_mr, tuned_mr, default_params, tuned_params])

    def _simulate_sota(self, algo, trace_path, cache_cap, params: Dict):
        param_str = ''
        for param_name, param_val in params.items():
            if param_str != '':
                param_str += ','
            param_str += f'{param_name}={param_val}'

        return run_libcachesim(cache_trace=trace_path, cache_alg=algo, cache_cap=cache_cap, params=param_str)

    def _simulate_not_sota(self, algo, trace_path, cache_cap, params: Dict):
        simulator = self._get_simulator(trace_path, cache_cap)
        with open(algo) as file:
            code_str = file.read()
        return simulator.simulate(
            code=code_str,
            code_id='simulate_not_sota',
            need_log=True,
            check_code_exists=False,
            fix_default_param=True,
            need_save=False,
            need_copy_code=True,
            default_params=params,
        )

    def _simulate(self, algo, trace_path, cache_cap, params, is_sota):
        if is_sota == True:
            return self._simulate_sota(algo, trace_path, cache_cap, params)
        else:
            return self._simulate_not_sota(algo, trace_path, cache_cap, params)

    def eval(
        self, trace_type: str, trace_file_name: str, train_frac: int, cache_cap_frac: float, algo: str, is_sota: bool
    ):
        # Check whether the entry has already be evaluated
        for entry in self.entries:
            if (
                entry.trace_type == trace_type
                and entry.trace_file_name == trace_file_name
                and entry.train_frac == train_frac
                and entry.cache_cap_frac == cache_cap_frac
                and entry.algo == algo
            ):
                logging.info(f'{entry!s} has already be simulated!')
                return entry

        # Prepare train and test traces
        train_trace_path = self._get_trace_path(
            trace_type=trace_type, trace_file_name=trace_file_name, train_frac=train_frac, is_train=True
        )
        test_trace_path = self._get_trace_path(
            trace_type=trace_type, trace_file_name=trace_file_name, train_frac=train_frac, is_train=False
        )
        full_trace_path = self._get_trace_path(
            trace_type=trace_type, trace_file_name=trace_file_name, train_frac=train_frac, is_train=None
        )
        if not is_sota == True:
            assert os.path.exists(algo)

        # Simulating
        full_trace = Trace(full_trace_path)
        cache_cap = int(full_trace.get_ndv() * 0.1)
        if cache_cap < 1:
            cache_cap = 1
        entry = Entry(
            trace_type=trace_type,
            trace_file_name=trace_file_name,
            train_frac=train_frac,
            cache_cap=cache_cap,
            cache_cap_frac=cache_cap_frac,
            algo=algo,
            is_sota=is_sota,
            init_param_mr_info=MissRatioInfo(None, None, None),
            tuned_param_mr_info=MissRatioInfo(None, None, None),
        )
        logging.info(f'Simulating {entry!s}')

        # Train parameters
        logging.info('\ttraining...')
        if is_sota == True:
            miss_ratio_info_tuple = self._tune_sota(algo=algo, trace_path=train_trace_path, cache_cap=cache_cap)
        else:
            miss_ratio_info_tuple = self._tune_not_sota(algo=algo, trace_path=train_trace_path, cache_cap=cache_cap)
        assert miss_ratio_info_tuple != None
        entry.init_param_mr_info.mr_train = miss_ratio_info_tuple[0]  # default_mr
        entry.tuned_param_mr_info.mr_train = miss_ratio_info_tuple[1]  # tuned_mr
        entry.init_param_mr_info.params = miss_ratio_info_tuple[2]  # default_param
        entry.tuned_param_mr_info.params = miss_ratio_info_tuple[3]  # tuned_param

        # Test parameters
        logging.info('\ttesting...')
        ## init_params
        logging.info(f'\t\tinit_params: {entry.init_param_mr_info.params}')
        entry.init_param_mr_info.mr_test = self._simulate(
            algo=algo,
            trace_path=test_trace_path,
            cache_cap=cache_cap,
            params=entry.init_param_mr_info.params,
            is_sota=is_sota,
        )
        ## tuned_params
        logging.info(f'\t\ttuned_params: {entry.tuned_param_mr_info.params}')
        if entry.tuned_param_mr_info.params == entry.init_param_mr_info.params:
            entry.tuned_param_mr_info.mr_test = entry.init_param_mr_info.mr_test
        else:
            entry.tuned_param_mr_info.mr_test = self._simulate(
                algo=algo,
                trace_path=test_trace_path,
                cache_cap=cache_cap,
                params=entry.tuned_param_mr_info.params,
                is_sota=is_sota,
            )

        # save
        self.entries.append(entry)
        write_to_file(
            dest_path=self.policy_eval_jsonl_path, contents=entry.to_jsonl() + '\n', is_append=True, is_json=False
        )

        return entry

    def plot_miss_ratio_percentile(
        self,
        trace_type: str,
        train_frac: int,
        cache_cap_frac: float,
        algo_list: List[str],
        png_path: str,
        use_init: bool,
        use_test: bool,
    ):
        """Args:
        - trace_filter (func):
            - input: trace_path (str)
            - output: True/False
        """
        if 'fifo' not in algo_list:
            algo_list.append('fifo')

        # load
        candid_entries = [
            e
            for e in self.entries
            if (
                e.algo in algo_list
                and e.cache_cap_frac == cache_cap_frac
                and e.trace_type == trace_type
                and e.train_frac == train_frac
            )
        ]
        m_algo_entry = {
            algo: sorted([e for e in candid_entries if e.algo == algo], key=lambda e: e.trace_file_name)
            for algo in algo_list
        }
        m_algo_mr: Dict[str, List] = dict()
        for algo in m_algo_entry:
            if algo == 'fifo':
                continue
            try:
                assert list([e.trace_file_name for e in m_algo_entry[algo]]) == list(
                    [e.trace_file_name for e in m_algo_entry['fifo']]
                )
            except Exception:
                logging.warning(f'{algo}, {[e.trace_file_name for e in m_algo_entry[algo]]}')
                continue
            m_algo_mr[algo] = list()
            for e, fifo_e in zip(m_algo_entry[algo], m_algo_entry['fifo']):
                if use_init == False:
                    e_mr_info = e.tuned_param_mr_info
                    fifo_mr_info = fifo_e.tuned_param_mr_info
                else:
                    e_mr_info = e.init_param_mr_info
                    fifo_mr_info = fifo_e.init_param_mr_info

                if use_test == True:
                    e_mr = e_mr_info.mr_test
                    fifo_mr = fifo_mr_info.mr_test
                else:
                    e_mr = e_mr_info.mr_train
                    fifo_mr = fifo_mr_info.mr_train
                if e_mr == None:
                    logging.warning(f'{algo}, e_mr=None')
                    break
                m_algo_mr[algo].append(miss_ratio_reduction(e_mr, fifo_mr))
        # plot
        plot_mr(m_algo_mr, png_path)
