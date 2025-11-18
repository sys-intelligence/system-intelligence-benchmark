import json
import logging
import os
from multiprocessing import Pool

import numpy as np
from Analyzer import Analyzer
from cache import CacheConfig, Trace
from Simulator import SimulatorCache, SimulatorConfig
from utils import miss_ratio_reduction, run_libcachesim, write_to_file


def cross_validate_simulate(simulator: SimulatorCache):
    return simulator.simulate(
        code='',
        code_id='cross_validate',
        need_log=False,
        check_code_exists=False,
        fix_default_param=False,
        need_save=False,
        need_copy_code=False,
        default_params=None,
    )


class CrossValidatorEntry:
    def __init__(
        self,
        # algo: if sota, algo_name; else, code_path
        algo: str,
        is_sota: bool,
        params: dict,
        mr: float,
        trace_path: str,
        cache_cap: int,
        cache_cap_frac: float,
    ):
        self.algo = algo
        self.is_sota = is_sota
        self.params = params
        self.mr = mr
        self.trace_path = trace_path
        self.cache_cap = cache_cap
        self.cache_cap_frac = cache_cap_frac

    @property
    def signature(self):
        """(basename(trace_path), cache_cap_frac, algo, params)"""
        return (
            os.path.basename(self.trace_path),
            self.cache_cap_frac,
            self.algo,
            self.params,
        )

    @classmethod
    def from_dict(cls, trace_cross_validate_entry_dict):
        return CrossValidatorEntry(
            algo=trace_cross_validate_entry_dict['algo'],
            is_sota=trace_cross_validate_entry_dict['is_sota'],
            params=trace_cross_validate_entry_dict['params'],
            mr=trace_cross_validate_entry_dict['mr'],
            trace_path=trace_cross_validate_entry_dict['trace_path'],
            cache_cap=trace_cross_validate_entry_dict['cache_cap'],
            cache_cap_frac=trace_cross_validate_entry_dict['cache_cap_frac'],
        )

    @classmethod
    def from_jsonl(cls, jsonl: str):
        return CrossValidatorEntry.from_dict(json.loads(jsonl))

    def to_dict(self):
        return {
            'algo': self.algo,
            'is_sota': self.is_sota,
            'params': self.params,
            'mr': self.mr,
            'trace_path': self.trace_path,
            'cache_cap': self.cache_cap,
            'cache_cap_frac': self.cache_cap_frac,
        }

    def to_jsonl(self):
        return json.dumps(self.to_dict())


class CrossValidator:
    cross_validate_jsonl_path = os.path.join(Analyzer.trace_analysis_folder, 'cross_validate.jsonl')

    def __init__(self):
        with open(self.cross_validate_jsonl_path) as file:
            file_lines = file.readlines()
        self.cross_validate_entries = [CrossValidatorEntry.from_jsonl(l) for l in file_lines]
        self.trace_analyzer = Analyzer()

    def _params_dict_to_str(self, params: dict):
        params_str = ''
        for key, value in params.items():
            if params_str != '':
                params_str += ','
            params_str += f'{key}={value}'
        return params_str

    def _get_candid_entries(self, filter_trace_path, filter_cache_cap_frac, filter_algo, filter_params):
        """Retrieved from cross_validate_entries"""

        def filter_entry(entry: CrossValidatorEntry):
            if filter_trace_path(entry.trace_path) == False:
                return False
            if filter_cache_cap_frac(entry.cache_cap_frac) == False:
                return False
            if filter_algo(entry.algo) == False:
                return False
            if filter_params(entry.params) == False:
                return False
            return True

        return [e for e in self.cross_validate_entries if filter_entry(e) == True]

    def _get_candid_params(self, filter_trace_path, filter_cache_cap_frac, filter_algo):
        """Retrieved from miss_ratio_entries."""
        candid_miss_ratio_entries = self.trace_analyzer._get_candid_entries(
            trace_filter=filter_trace_path, cache_cap_frac_filter=filter_cache_cap_frac, algo_filter=filter_algo
        )
        candid_params_str = set([json.dumps(e.miss_ratio_info.tuned_params) for e in candid_miss_ratio_entries])
        if len(candid_miss_ratio_entries) > 0:
            candid_params_str.add(json.dumps(candid_miss_ratio_entries[0].miss_ratio_info.default_params))
        return [dict(json.loads(ps)) if ps != 'null' else None for ps in candid_params_str]

    def _add_entry(self, new_entry: CrossValidatorEntry):
        self.cross_validate_entries.append(new_entry)
        write_to_file(
            dest_path=self.cross_validate_jsonl_path,
            contents=new_entry.to_jsonl() + '\n',
            is_append=True,
            is_json=False,
        )

    def _get_simulator(self, trace_path_list: list, cache_cap_frac: float):
        trace_cap_list = []
        for trace_path in trace_path_list:
            trace = Trace(trace_path, True)
            cap = int(trace.get_ndv() * cache_cap_frac)
            if cap < 1:
                cap = 1
            trace_cap_list.append(cap)

        simulator_list = [
            SimulatorCache(
                SimulatorConfig(
                    name='Cache',
                    config=CacheConfig(
                        capacity=trace_cap,
                        consider_obj_size=False,
                        trace_path=trace_path,
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
            for (trace_path, trace_cap) in zip(trace_path_list, trace_cap_list)
        ]

        return simulator_list

    def _simulate(
        self,
        algo: str,  # algo: if sota, algo_name; else, code_path
        is_sota: bool,
        params: dict,
        trace_path_list: list,
        cache_cap_frac: float,
    ):
        logging.info(f'Simulating {(algo, params)}')
        if is_sota == False:
            assert os.path.exists(algo)

        # check cross_validate_entries
        cross_validate_entries = self._get_candid_entries(
            filter_trace_path=lambda p: os.path.basename(p) in [os.path.basename(t) for t in trace_path_list],
            filter_cache_cap_frac=lambda ccf: ccf == cache_cap_frac,
            filter_algo=lambda alg: alg == algo,
            filter_params=lambda p: p == params,
        )
        for trace_path in [e.trace_path for e in cross_validate_entries]:
            logging.info(f'\t{(algo, params, trace_path, cache_cap_frac)} already existed in cross_validate.jsonl')

        first_cleaned_trace_path_list = [
            t
            for t in trace_path_list
            if os.path.basename(t) not in [os.path.basename(e.trace_path) for e in cross_validate_entries]
        ]
        if len(first_cleaned_trace_path_list) == 0:
            return

        # check miss_ratio_entries
        candid_miss_ratio_entries = self.trace_analyzer._get_candid_entries(
            trace_filter=lambda p: os.path.basename(p) in [os.path.basename(t) for t in first_cleaned_trace_path_list],
            cache_cap_frac_filter=lambda ccf: ccf == cache_cap_frac,
            algo_filter=lambda alg: alg == algo,
        )
        miss_ratio_entries = [
            e
            for e in candid_miss_ratio_entries
            if e.miss_ratio_info.tuned_params == params or e.miss_ratio_info.default_params == params
        ]
        for entry in miss_ratio_entries:
            if entry.miss_ratio_info.tuned_params == params:
                mr = entry.miss_ratio_info.tuned_mr
            else:
                assert entry.miss_ratio_info.default_params == params
                mr = entry.miss_ratio_info.default_mr
            new_cross_validator_entry = CrossValidatorEntry(
                algo=algo,
                is_sota=is_sota,
                params=params,
                mr=mr,
                trace_path=entry.trace_path,
                cache_cap=entry.cache_cap,
                cache_cap_frac=cache_cap_frac,
            )
            self._add_entry(new_cross_validator_entry)
            logging.info(f'\t{(algo, params, entry.trace_path, cache_cap_frac)} already existed in miss_ratio.jsonl')

        cleaned_trace_path_list = [
            t
            for t in first_cleaned_trace_path_list
            if os.path.basename(t) not in [os.path.basename(e.trace_path) for e in miss_ratio_entries]
        ]

        if len(cleaned_trace_path_list) == 0:
            return

        simulator_list = self._get_simulator(cleaned_trace_path_list, cache_cap_frac)
        # is_sota = True
        if is_sota == True:
            for sim in simulator_list:
                mr = run_libcachesim(
                    cache_trace=sim.config.trace_path,
                    cache_alg=algo,
                    cache_cap=sim.config.capacity,
                    params=self._params_dict_to_str(params),
                )
                new_cross_validator_entry = CrossValidatorEntry(
                    algo=algo,
                    is_sota=is_sota,
                    params=params,
                    mr=mr,
                    trace_path=sim.config.trace_path,
                    cache_cap=sim.config.capacity,
                    cache_cap_frac=cache_cap_frac,
                )
                self._add_entry(new_cross_validator_entry)
            return

        # is_sota = False
        example_sim = simulator_list[0]
        copy_dst = os.path.join(example_sim.system_path, 'My.py')
        with open(algo) as file:
            raw_code = file.read()
        assert os.path.exists(copy_dst)
        with open(copy_dst, 'w') as file:
            file.write(example_sim._fix_default_param_for_code(raw_code, params))
        with Pool(len(simulator_list) * 2) as p:
            mr_list = p.map(cross_validate_simulate, simulator_list)
        assert len(mr_list) == len(simulator_list)
        for mr, sim in zip(mr_list, simulator_list):
            new_cross_validator_entry = CrossValidatorEntry(
                algo=algo,
                is_sota=is_sota,
                params=params,
                mr=mr,
                trace_path=sim.config.trace_path,
                cache_cap=sim.config.capacity,
                cache_cap_frac=cache_cap_frac,
            )
            self._add_entry(new_cross_validator_entry)

    def plot_miss_ratio_percentile(self, trace_filter, algo_list: list, cache_cap_frac: float, png_path: str):
        if 'fifo' not in algo_list:
            algo_list.append('fifo')

        # load
        m_algo_entry = dict()  # list of entries for each algorithm in algo_list
        for algo in algo_list:
            # collect candid params
            candid_params = self._get_candid_params(
                filter_trace_path=trace_filter,
                filter_cache_cap_frac=lambda ccf: ccf == cache_cap_frac,
                filter_algo=lambda alg: alg == algo,
            )
            # categorize them by params
            candid_params_str = set([json.dumps(p) for p in candid_params])
            m_params_str_to_entries = {
                ps: sorted(
                    self._get_candid_entries(
                        filter_trace_path=trace_filter,
                        filter_cache_cap_frac=lambda ccf: ccf == cache_cap_frac,
                        filter_algo=lambda alg: alg == algo,
                        filter_params=lambda p: json.dumps(p) == ps,
                    ),
                    key=lambda e: os.path.basename(e.trace_path),
                )
                for ps in candid_params_str
            }
            # debug
            entries_list = list(m_params_str_to_entries.values())
            for entries in entries_list[1:]:
                assert [os.path.basename(e.trace_path) for e in entries] == [
                    os.path.basename(e.trace_path) for e in entries_list[0]
                ]
            assert len(entries_list[0]) == 24
            # select opt params
            sorted_params_str = sorted(
                list(m_params_str_to_entries.keys()),
                key=lambda ps: tuple(
                    [np.percentile([e.mr for e in m_params_str_to_entries[ps]], perc) for perc in [90, 75, 50, 25, 10]]
                ),
            )
            target_ps = sorted_params_str[0]
            # set m_algo_entry
            m_algo_entry[algo] = m_params_str_to_entries[target_ps]

        m_algo_mr = dict()  # list of miss ratios for each algorithm in algo_list
        for algo in m_algo_entry:
            if algo == 'fifo':
                continue
            assert list([os.path.basename(e.trace_path) for e in m_algo_entry[algo]]) == list(
                [os.path.basename(e.trace_path) for e in m_algo_entry['fifo']]
            )
            m_algo_mr[algo] = list()
            for e, fifo_e in zip(m_algo_entry[algo], m_algo_entry['fifo']):
                m_algo_mr[algo].append(miss_ratio_reduction(e.mr, fifo_e.mr))

        self.trace_analyzer._plot(m_algo_mr, png_path)

    def simulate(
        self,
        algo: str,  # algo: if sota, algo_name; else, code_path
        is_sota: bool,
        trace_path_list: list,
        cache_cap_frac: float,
    ):
        """The simulation is executed in parallel."""
        candid_params = self._get_candid_params(
            filter_trace_path=lambda p: os.path.basename(p) in [os.path.basename(t) for t in trace_path_list],
            filter_cache_cap_frac=lambda ccf: ccf == cache_cap_frac,
            filter_algo=lambda alg: alg == algo,
        )
        for param in candid_params:
            self._simulate(
                algo=algo,
                is_sota=is_sota,
                params=param,
                trace_path_list=trace_path_list,
                cache_cap_frac=cache_cap_frac,
            )
