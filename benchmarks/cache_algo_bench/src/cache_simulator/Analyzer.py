import itertools
import json
import logging
import os

import matplotlib.pyplot as plt
import numpy as np

logging.disable(logging.DEBUG)
from typing import Dict

from cache import CacheConfig, Trace
from Simulator import SimulatorCache, SimulatorConfig
from utils import miss_ratio_reduction, tune_libcachesim, write_to_file


class MissRatioInfo:
    def __init__(self, default_mr: float, default_params: Dict, tuned_mr: float, tuned_params: Dict):
        self.default_mr = default_mr
        self.default_params = default_params
        self.tuned_mr = tuned_mr
        self.tuned_params = tuned_params
        assert default_mr >= 0 and default_mr <= 1
        assert tuned_mr >= 0 and tuned_mr <= 1

    def to_dict(self):
        return {
            'default_mr': self.default_mr,
            'tuned_mr': self.tuned_mr,
            'default_params': self.default_params,
            'tuned_params': self.tuned_params,
        }


class AnalyzerEntry:
    def __init__(
        self,
        trace_path: str,
        cache_cap: int,
        cache_cap_frac: float,
        algo: str,
        is_sota: bool,
        default_mr: float,
        tuned_mr: float,
        default_params: dict,
        tuned_params: dict,
    ):
        self.trace_path = trace_path
        self.cache_cap = cache_cap
        self.cache_cap_frac = cache_cap_frac
        self.algo = algo
        self.is_sota = is_sota
        self.miss_ratio_info = MissRatioInfo(
            default_mr=default_mr, default_params=default_params, tuned_mr=tuned_mr, tuned_params=tuned_params
        )

    @property
    def signature(self):
        """(trace_path, cache_cap_frac, algo)"""
        return (
            # self.trace_path,
            os.path.basename(self.trace_path),
            self.cache_cap_frac,
            self.algo,
        )

    @classmethod
    def from_dict(cls, trace_analysis_entry_dict):
        return AnalyzerEntry(
            trace_path=trace_analysis_entry_dict['trace_path'],
            cache_cap=trace_analysis_entry_dict['cache_cap'],
            cache_cap_frac=trace_analysis_entry_dict['cache_cap_frac'],
            algo=trace_analysis_entry_dict['algo'],
            is_sota=trace_analysis_entry_dict['is_sota'],
            default_mr=trace_analysis_entry_dict['default_mr'],
            tuned_mr=trace_analysis_entry_dict['tuned_mr'],
            default_params=trace_analysis_entry_dict['default_params'],
            tuned_params=trace_analysis_entry_dict['tuned_params'],
        )

    @classmethod
    def from_jsonl(cls, jsonl: str):
        trace_analysis_entry_dict = json.loads(jsonl)
        return AnalyzerEntry.from_dict(trace_analysis_entry_dict)

    def to_dict(self):
        trace_analysis_entry_dict = {
            'trace_path': self.trace_path,
            'cache_cap': self.cache_cap,
            'cache_cap_frac': self.cache_cap_frac,
            'algo': self.algo,
            'is_sota': self.is_sota,
        }
        trace_analysis_entry_dict.update(self.miss_ratio_info.to_dict())
        return trace_analysis_entry_dict

    def to_jsonl(self):
        return json.dumps(self.to_dict())


class Analyzer:
    # trace_analysis_folder = os.path.join(os.path.dirname(os.path.abspath(__file__)), "analysis")
    trace_analysis_folder = '/home/v-ruiyingma/llm4sys/cache/trace_analysis'
    miss_ratio_jsonl_path = os.path.join(trace_analysis_folder, 'miss_ratio.jsonl')

    def __init__(self):
        with open(self.miss_ratio_jsonl_path) as file:
            file_lines = file.readlines()
        self.entries = [AnalyzerEntry.from_jsonl(l) for l in file_lines]

    def get_trace_ndv(self, trace_path, range_s=None, range_e=None):
        trace = Trace(trace_path=trace_path, next_vtime_set=True)
        return trace.get_ndv(range_s=range_s, range_e=range_e)

    def _get_candid_entries(self, trace_filter, cache_cap_frac_filter, algo_filter):
        def entry_filter(entry: AnalyzerEntry):
            if trace_filter(entry.trace_path) == False:
                return False
            if cache_cap_frac_filter(entry.cache_cap_frac) == False:
                return False
            if algo_filter(entry.algo) == False:
                return False
            return True

        return [e for e in self.entries if entry_filter(e) == True]

    def simulate(self, trace_path: str, cache_cap_frac: float, algo: str, is_sota: bool):
        """Args:
        - trace_path (str): absolute path to the trace
        - cache_cap_frac (float): cache capacity / trace.ndv
        - algo (str):
            - if `is_sota` == True, this is the sota algorithm name
            - else, this is the absolute path to the code
        - is_sota (bool): whether this is sota algorithm that can be simulated by libcachesim
        """
        assert os.path.exists(trace_path)
        if not is_sota == True:
            assert os.path.exists(algo)

        # algo_name = algo if is_sota == True else os.path.basename(algo).replace(".py", "")
        algo_name = algo

        candid_entries = self._get_candid_entries(
            trace_filter=lambda p: os.path.basename(p) == os.path.basename(trace_path),
            cache_cap_frac_filter=lambda ccf: ccf == cache_cap_frac,
            algo_filter=lambda alg: alg == algo,
        )
        if len(candid_entries) > 0:
            assert len(candid_entries) == 1
            logging.info(f'({trace_path}, {algo}, {cache_cap_frac}) has already been simulated')
            return candid_entries[0]

        logging.info(f'Simulating ({trace_path}, {algo}, {cache_cap_frac})...')
        cache_cap = int(self.get_trace_ndv(trace_path) * cache_cap_frac)
        if cache_cap < 1:
            cache_cap = 1

        if is_sota == True:
            miss_ratio_info_tuple = tune_libcachesim(
                trace=trace_path,
                alg=algo,
                cache_cap=cache_cap,
            )
            assert miss_ratio_info_tuple != None
            entry = AnalyzerEntry(
                trace_path=trace_path,
                cache_cap=cache_cap,
                cache_cap_frac=cache_cap_frac,
                algo=algo_name,
                is_sota=is_sota,
                default_mr=miss_ratio_info_tuple[0],
                tuned_mr=miss_ratio_info_tuple[1],
                default_params=miss_ratio_info_tuple[2],
                tuned_params=miss_ratio_info_tuple[3],
            )
        else:
            simulator = SimulatorCache(
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
            code_path = algo
            algo_name = algo
            code_id = algo_name
            with open(code_path) as file:
                code = file.read()
            default_mr = simulator.simulate(
                code=code,
                code_id=code_id,
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
            entry = AnalyzerEntry(
                trace_path=trace_path,
                cache_cap=cache_cap,
                cache_cap_frac=cache_cap_frac,
                algo=algo_name,
                is_sota=is_sota,
                default_mr=default_mr,
                tuned_mr=tuned_mr,
                default_params=default_params,
                tuned_params=tuned_params,
            )

        self.entries.append(entry)
        write_to_file(
            dest_path=self.miss_ratio_jsonl_path, contents=entry.to_jsonl() + '\n', is_append=True, is_json=False
        )
        return entry

    def _plot(self, m_algo_mr: dict, png_path):
        markers = itertools.cycle('<^osv>v*p')
        colors = itertools.cycle(reversed(['#b2182b', '#ef8a62', '#fddbc7', '#d1e5f0', '#67a9cf', '#2166ac']))
        algo_list = list(m_algo_mr.keys())
        assert 'fifo' not in algo_list
        # plot
        plt.figure(figsize=(28, 8))
        percentiles = [10, 25, 50, 75, 90]
        # algo_list.remove("fifo")
        for perc in percentiles:
            y = [np.percentile(m_algo_mr[algo], perc) for algo in algo_list]
            plt.scatter(range(len(y)), y, label=f'P{perc}', marker=next(markers), color=next(colors), s=480)
            if perc == 50:
                # Mean
                y = [np.mean(m_algo_mr[algo]) for algo in algo_list]
                plt.scatter(range(len(y)), y, label='Mean', marker=next(markers), color=next(colors), s=480)
        if plt.ylim()[0] < -0.1:
            plt.ylim(bottom=-0.04)
        plt.xticks(
            range(len(algo_list)), [os.path.basename(a).replace('.py', '') for a in algo_list], fontsize=32, rotation=90
        )
        plt.ylabel('Miss ratio reduction from FIFO')
        plt.grid(linestyle='--')
        plt.legend(
            ncol=8,
            loc='upper left',
            fontsize=38,
            bbox_to_anchor=(-0.02, 1.2),
            frameon=False,
        )
        plt.savefig(png_path, bbox_inches='tight')
        plt.clf()

    def plot_miss_ratio_percentile(
        self, trace_filter, algo_list: list, cache_cap_frac: float, png_path: str, use_default: bool
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
            if e.algo in algo_list and e.cache_cap_frac == cache_cap_frac and trace_filter(e.trace_path) == True
        ]
        m_algo_entry = {
            algo: sorted([e for e in candid_entries if e.algo == algo], key=lambda e: e.trace_path)
            for algo in algo_list
        }
        m_algo_mr = dict()
        for algo in m_algo_entry:
            if algo == 'fifo':
                continue
            assert list([os.path.basename(e.trace_path) for e in m_algo_entry[algo]]) == list(
                [os.path.basename(e.trace_path) for e in m_algo_entry['fifo']]
            )
            m_algo_mr[algo] = list()
            for e, fifo_e in zip(m_algo_entry[algo], m_algo_entry['fifo']):
                if use_default == False:
                    m_algo_mr[algo].append(
                        miss_ratio_reduction(e.miss_ratio_info.tuned_mr, fifo_e.miss_ratio_info.tuned_mr)
                    )
                else:
                    m_algo_mr[algo].append(
                        miss_ratio_reduction(e.miss_ratio_info.default_mr, fifo_e.miss_ratio_info.default_mr)
                    )
        self._plot(m_algo_mr, png_path)
