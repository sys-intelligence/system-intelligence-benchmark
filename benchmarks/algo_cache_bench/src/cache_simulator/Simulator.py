import logging
import os
import signal
import time
import traceback
from abc import ABC, abstractmethod
from datetime import datetime

from cache_simulator.cache import Cache, CacheConfig, CacheObj, Trace
from cache_simulator.utils import extract_string, get_type_and_value, is_expr, modify_string, write_to_file

# from openbox import Optimizer
# from openbox import space as sp


# Define a custom exception for timeout
class TimeoutException(Exception):
    pass


# Function to handle the timeout
def timeout_handler(signum, frame):
    raise TimeoutException('Function execution timed out')


# Decorator to add a timeout to a function
def timeout():
    seconds = SimulatorBase.get_timeout_limit()

    def decorator(func):
        def wrapper(*args, **kwargs):
            # Set the signal handler and alarm
            signal.signal(signal.SIGALRM, timeout_handler)
            signal.alarm(seconds)
            try:
                result = func(*args, **kwargs)
            finally:
                # Disable the alarm
                signal.alarm(0)
            return result

        return wrapper

    return decorator


class SimulatorConfig:
    def __init__(
        self,
        name,
        config,  # extra config for your system
        system_path,  # the path to your system folder (e.g., the path to cache/)
        tune_runs: int,
        code_folder: str,
        tune_int_upper: int,
    ):
        self.name = name
        self.config = config
        assert os.path.exists(system_path)
        self.system_path = system_path
        self.tune_runs = tune_runs
        self.code_folder = code_folder
        self.tune_int_upper = tune_int_upper


class SimulatorBase(ABC):
    timeout_limit: int = 600

    def __init__(self, simulator_config: SimulatorConfig) -> None:
        self.name = simulator_config.name
        self.config = simulator_config.config
        assert os.path.exists(simulator_config.system_path)
        self.system_path = simulator_config.system_path
        self.tune_runs = simulator_config.tune_runs
        self.code_folder = simulator_config.code_folder
        self.tune_int_upper = simulator_config.tune_int_upper
        # latent variables
        self.code_path = None  # the place the code is stored
        # statistics
        self.latency = 0.0

    @classmethod
    def get_timeout_limit(cls):
        return cls.timeout_limit

    @abstractmethod
    def simulate(self, code, code_id, need_log=True):
        """Run the code to compute its score. If passed, store the code to `self.code_path`. If failed, store the error log `self.code_path`.

        Args:
        - code (str)
        - code_id (str)
        Return: mr
        """
        pass

    @abstractmethod
    def tune(self, code, code_id, fixed_default_param: bool, need_log: bool = True):
        """Tune the code's parameters. The code is assured to pass `run()`. Write errors to `self.code_path`
        Args:
        - code (str)
        - code_id (str)
        Return: tuned_mr, default_params, tuned_params
        """
        pass

    def to_dict(self):
        return {
            'name': self.name,
            'config': self.config.to_dict(),
            'system_path': self.system_path,
            'timeout_limit': self.timeout_limit,
            'tune_runs': self.tune_runs,
            'code_folder': self.code_folder,
            'tune_int_upper': self.tune_int_upper,
            'latency': self.latency,
        }


class SimulatorCache(SimulatorBase):
    def __init__(
        self,
        simulator_config: SimulatorConfig,
    ) -> None:
        super().__init__(simulator_config)
        assert isinstance(self.config, CacheConfig)
        self.name = 'Cache'
        if self.tune_int_upper == None:
            self.tune_int_upper = self.config.capacity

    def _read_trace(self):
        assert isinstance(self.config, CacheConfig)
        trace = Trace(self.config.trace_path, True)
        if self.config.consider_obj_size == True:
            return [CacheObj(key=str(entry.key), size=entry.size, consider_obj_size=True) for entry in trace.entries]
        else:
            return [CacheObj(key=str(entry.key), size=1, consider_obj_size=False) for entry in trace.entries]

    @timeout()
    def _run(self, code, need_copy_code: bool = True):
        if need_copy_code == True:
            with open(os.path.join(self.system_path, 'My.py'), 'w') as file:
                file.write(code)

        cache = Cache(config=self.config)
        trace = self._read_trace()
        assert cache.access_count == 0
        assert cache.hit_count == 0
        for oid, obj in enumerate(trace):
            cache.get(obj)
        return round(1 - cache.hit_count / cache.access_count, 4)

    def _fix_default_param_for_code(self, code, default_params: dict = None):
        config_space = self._get_configspace(code, True)
        if config_space != None:
            raw_params = dict(config_space).copy()
            if default_params == None:
                params = {k: v.default_value for k, v in raw_params.items()}
            else:
                params = default_params
            new_code = self._update_code(code, params)
            return new_code
        return code

    @timeout()
    def simulate(
        self,
        code,
        code_id,
        need_log=True,
        check_code_exists: bool = True,
        fix_default_param: bool = False,
        need_save=True,
        need_copy_code: bool = True,
        default_params: dict = None,
    ):
        self.code_path = os.path.join(self.code_folder, f'{code_id}.py')
        if check_code_exists == True:
            assert not os.path.exists(self.code_path)
        if fix_default_param == True:
            code = self._fix_default_param_for_code(code, default_params)
        start = time.time()
        try:
            miss_ratio = self._run(code, need_copy_code)
        except Exception as error:
            end = time.time()
            self.latency += end - start
            logging.warning(f'New code: {code_id}\n\tFAIL...\n\tError message: {error!r}')
            if need_log:
                self._log_error(code_id, '(Simulation) ' + repr(error), traceback.format_exc().strip())
            self._reset(need_copy_code)
            return None
        end = time.time()
        self.latency += end - start
        assert miss_ratio != None
        assert self.code_path != None
        if need_save == True:
            write_to_file(dest_path=self.code_path, contents=code.strip(), is_append=False, is_json=False)
        return miss_ratio

    def tune(self, code, code_id, fixed_default_param: bool, need_log: bool = True, need_copy_code: bool = True):
        self.code_path = os.path.join(self.code_folder, f'{code_id}.py')
        config_space = self._get_configspace(code, fixed_default_param)
        if config_space == None:
            # No tunable parameters
            return None, None, None
        default_params = dict()
        for k, v in dict(
            config_space
        ).items():  # https://automl.github.io/ConfigSpace/latest/api/ConfigSpace/configuration/#ConfigSpace.configuration.Configuration.get_dictionary
            default_params[k] = v.default_value

        def objective(config_space: sp.Configuration):
            params = dict(config_space).copy()
            assert len(params) > 0
            new_code = self._update_code(code, params)
            try:
                score = self._run(code=new_code, need_copy_code=need_copy_code)
            except Exception:
                self._reset(need_copy_code)
                score = 1.0
            assert score != None
            return dict(objectives=[score])  # tune for the minimal

        opt = Optimizer(
            objective_function=objective,
            config_space=config_space,
            num_objectives=1,
            num_constraints=0,
            max_runs=self.tune_runs,
            surrogate_type='prf',  # 'prf' for practical problems; 'gp' for mathematical problems
            visualization='none',
        )

        opt_score = None
        tuned_parms = None
        error_log = None

        start = time.time()
        try:
            history = opt.run()
        except Exception as error:
            error_log = True
            logging.info(f'Tuning code {code_id}: FAIL...\n\tError message: {error!r}')
            if need_log:
                self._log_error(code_id, '(Tuning) ' + repr(error), traceback.format_exc().strip())
            self._reset(need_copy_code)
        end = time.time()
        self.latency += end - start

        if error_log == None and len(history.get_incumbents()) > 0:
            opt_score = history.get_incumbent_value()
            tuned_parms = dict(history.get_incumbent_configs()[0]).copy()

        return opt_score, default_params, tuned_parms

    def _get_configspace(self, code, fixed_default=False):
        """Args:
        - code (str)
        - fixed_default (bool): whether change default params to our fixed values
            - int: 3
            - float: 0.42
            - bool: 1
        Return:
        - space (openbox.Space | None) if code has tunable parameters,
        - or `None`
        """
        space = sp.Space()

        tp_pattern = r'(# Put tunable constant parameters below\s*\n)(.*?)(?=^# Put the metadata specifically maintained by the policy below)'

        tunable_parameters: str = extract_string(
            text=code,
            regex=tp_pattern,
            group_id=2,
        )

        if tunable_parameters == None or tunable_parameters.strip() == '':
            return None

        candid_exprs = tunable_parameters.split('\n')
        optimizer_params = []
        for cexpr in candid_exprs:
            if not is_expr(cexpr):
                continue
            rhs_pattern = r'=\s*(.*?)\s*(#.*)?$'
            rhs = extract_string(text=cexpr, regex=rhs_pattern, group_id=1)
            if rhs == None:
                continue
            type_and_value = get_type_and_value(rhs)
            if type_and_value == None:
                continue
            assert len(type_and_value) == 2
            var_name = str(len(optimizer_params))
            var_type = type_and_value[0]
            if var_type == bool:
                var_lower = 0
                var_upper = 1
                var_default = 1 if type_and_value[1] else 0
                if fixed_default == True:
                    var_default = 1
                optimizer_params.append(sp.Int(var_name, var_lower, var_upper, default_value=var_default))
            elif var_type == int:
                var_default = int(type_and_value[1])
                if fixed_default == True:
                    var_default = 3
                var_lower = min(var_default, 1)
                var_upper = var_lower
                assert self.tune_int_upper != None
                var_upper = self.tune_int_upper
                var_upper = max(var_upper, 2 * var_default, var_lower)
                optimizer_params.append(sp.Int(var_name, var_lower, var_upper, default_value=var_default))
            else:
                assert var_type == float
                var_default = float(type_and_value[1])
                if fixed_default == True:
                    var_default = 0.42
                var_lower = min(var_default, 0.0)
                var_upper = max(var_default, 1.0)
                optimizer_params.append(sp.Real(var_name, var_lower, var_upper, default_value=var_default))

        if len(optimizer_params) == 0:
            return None

        space.add_variables(optimizer_params)
        return space

    def _update_code(self, code, params):
        """Update the code string with current config space
        Args:
        - code (str)
        - params (dict)

        Return:
        - new_code (str)
        """
        assert params != None
        tp_pattern = r'(# Put tunable constant parameters below\s*\n)(.*?)(?=^# Put the metadata specifically maintained by the policy below)'

        tunable_parameters = extract_string(
            text=code,
            regex=tp_pattern,
            group_id=2,
        )

        assert tunable_parameters != None

        candid_exprs = tunable_parameters.split('\n')
        new_cexprs = []
        param_id = 0
        for cexpr in candid_exprs:
            new_cexprs.append(cexpr)
            if not is_expr(cexpr):
                continue
            rhs_pattern = r'=\s*(.*?)\s*(#.*)?$'
            rhs = extract_string(text=cexpr, regex=rhs_pattern, group_id=1)
            if rhs == None:
                continue
            type_and_value = get_type_and_value(rhs)
            if type_and_value == None:
                continue
            assert len(type_and_value) == 2
            new_cexpr = modify_string(
                text=cexpr, regex=rhs_pattern, group_id=1, modification=str(params[str(param_id)])
            )
            new_cexprs[-1] = new_cexpr
            param_id += 1

        assert param_id == len(params)

        assert len(new_cexprs) == len(candid_exprs)
        new_tunable_parameters = '\n'.join(new_cexprs)
        new_code = modify_string(text=code, regex=tp_pattern, group_id=2, modification=new_tunable_parameters)
        return new_code

    def _reset(self, need_copy_code: bool = True):
        if need_copy_code == True:
            with open(os.path.join(self.system_path, 'My.py'), 'w') as file:
                file.write('')
        # self.code_path = None

    def _log_error(self, error_code_id, error_msg, traceback_msg=''):
        assert self.code_path != None
        error_code_path = self.code_path.replace('.py', '.error')
        assert error_code_path.endswith('.error')
        error_log = (
            f"**************************************************{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}**************************************************\n"
            + f'[code_id]: {error_code_id}\n[error_msg]: {error_msg}\n[traceback_msg]:\n{traceback_msg}'
            + '\n=======================================================================================================================\n\n'
        )
        write_to_file(dest_path=error_code_path, contents=error_log, is_append=True, is_json=False)
