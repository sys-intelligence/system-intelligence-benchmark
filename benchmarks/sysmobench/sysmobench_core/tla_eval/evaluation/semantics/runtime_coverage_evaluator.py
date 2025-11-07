"""
Runtime Coverage Evaluator: Semantic-level evaluation using simulation mode.

This evaluator uses TLC's simulation mode to evaluate the runtime behavior of
TLA+ specifications. It runs multiple simulations to collect coverage data and
identifies error-prone actions.

Key differences from coverage_evaluator:
1. Uses simulation mode instead of model checking (explores more, doesn't stop on first error)
2. Runs multiple simulations to maximize coverage
3. Tracks and excludes error-prone actions from the final metric
4. Final metric = (covered_actions - error_actions) / total_actions
"""

import os
import re
import tempfile
import shutil
import logging
import time
import subprocess
from pathlib import Path
from typing import Dict, List, Any, Tuple, Optional, Set
from dataclasses import dataclass, field
import random

from ...models.base import GenerationResult
from ...utils.output_manager import get_output_manager
from .runtime_check import ConfigGenerator
from ..base.evaluator import BaseEvaluator
from ..base.result_types import SemanticEvaluationResult
from .coverage_evaluator import TLCCoverageParser, CoverageData

logger = logging.getLogger(__name__)


@dataclass
class SimulationRun:
    """Data for a single simulation run"""
    run_id: int
    seed: int
    coverage_data: CoverageData
    error_info: Optional[Dict[str, Any]] = None
    output: str = ""
    success: bool = True


@dataclass
class RuntimeCoverageData:
    """Aggregated runtime coverage data from multiple simulations"""

    # All actions found in the specification
    all_actions: Set[str] = field(default_factory=set)

    # Actions that were successfully executed at least once
    covered_actions: Set[str] = field(default_factory=set)

    # Actions that led to errors
    error_actions: Set[str] = field(default_factory=set)

    # Successful actions (covered - error)
    successful_actions: Set[str] = field(default_factory=set)

    # Individual simulation runs
    simulation_runs: List[SimulationRun] = field(default_factory=list)

    # Summary statistics
    total_simulations: int = 0
    successful_simulations: int = 0
    failed_simulations: int = 0

    def calculate_runtime_coverage(self) -> float:
        """Calculate the runtime coverage metric"""
        if not self.all_actions:
            return 0.0
        self.successful_actions = self.covered_actions - self.error_actions
        logger.debug(f"Calculating runtime coverage:")
        logger.debug(f"  covered_actions = {self.covered_actions}")
        logger.debug(f"  error_actions = {self.error_actions}")
        logger.debug(f"  successful_actions = covered - error = {self.successful_actions}")
        return len(self.successful_actions) / len(self.all_actions)


class RuntimeCoverageEvaluator(BaseEvaluator):
    """
    Evaluator for TLA+ runtime coverage using simulation mode.

    Runs multiple simulations to maximize coverage and identify error-prone actions.
    """

    def __init__(self,
                 num_simulations: int = 20,
                 simulation_depth: int = 50,
                 traces_per_simulation: int = 50,
                 tlc_timeout: int = 30,
                 coverage_interval: int = 1):
        """
        Initialize runtime coverage evaluator.

        Args:
            num_simulations: Number of simulation runs
            simulation_depth: Maximum depth for each simulation trace
            traces_per_simulation: Number of traces per simulation
            tlc_timeout: Timeout for each TLC simulation in seconds
            coverage_interval: Interval for coverage statistics in minutes
        """
        super().__init__(timeout=tlc_timeout * num_simulations)
        self.num_simulations = num_simulations
        self.simulation_depth = simulation_depth
        self.traces_per_simulation = traces_per_simulation
        self.tlc_timeout = tlc_timeout
        self.coverage_interval = coverage_interval
        self.parser = TLCCoverageParser()
        # Get TLA+ tools path directly
        self.tla_tools_path = self._get_tla_tools_path()

    def _get_tla_tools_path(self):
        """Get path to TLA+ tools"""
        from ...utils.setup_utils import get_tla_tools_path
        return get_tla_tools_path()

    def evaluate(self,
                generation_result: GenerationResult,
                task_name: str,
                method_name: str,
                model_name: str,
                spec_module: str = None,
                spec_file_path: str = None,
                config_file_path: str = None) -> SemanticEvaluationResult:
        """
        Evaluate runtime coverage of a TLA+ specification.
        """
        logger.info(f"Runtime coverage evaluation: {task_name}/{method_name}/{model_name}")

        # Create output directory
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="runtime_coverage",
            task=task_name,
            method=method_name,
            model=model_name
        )
        logger.info(f"Using output directory: {output_dir}")

        # Create evaluation result
        result = SemanticEvaluationResult(task_name, method_name, model_name)

        # Set generation time from metadata if available
        if generation_result and hasattr(generation_result, 'metadata') and 'latency_seconds' in generation_result.metadata:
            result.generation_time = generation_result.metadata['latency_seconds']

        try:
            # Prepare specification files (similar to coverage_evaluator)
            final_spec_path, final_config_path = self._prepare_spec_files(
                generation_result, spec_file_path, config_file_path,
                output_dir, task_name, model_name, spec_module
            )

            result.specification_file = str(final_spec_path)

            # Run multiple simulations
            logger.info(f"Running {self.num_simulations} simulations...")
            runtime_data = RuntimeCoverageData()

            start_time = time.time()

            for i in range(self.num_simulations):
                seed = random.randint(1, 1000000)
                logger.info(f"Simulation {i+1}/{self.num_simulations} with seed {seed}")

                simulation_run = self._run_single_simulation(
                    final_spec_path, final_config_path,
                    output_dir, i+1, seed
                )

                runtime_data.simulation_runs.append(simulation_run)
                runtime_data.total_simulations += 1

                if simulation_run.success:
                    runtime_data.successful_simulations += 1
                else:
                    runtime_data.failed_simulations += 1

                # Aggregate coverage data
                self._aggregate_coverage(runtime_data, simulation_run)

                # Process errors
                if simulation_run.error_info:
                    self._process_error(runtime_data, simulation_run)

            result.model_checking_time = time.time() - start_time

            # Calculate final metric
            coverage_score = runtime_data.calculate_runtime_coverage()

            logger.info(f"\n{'='*60}")
            logger.info("Runtime Coverage Summary:")
            logger.info(f"  Total actions in spec: {len(runtime_data.all_actions)}")
            logger.info(f"    All actions: {sorted(runtime_data.all_actions)}")
            logger.info(f"  Covered actions: {len(runtime_data.covered_actions)}")
            logger.info(f"    Covered list: {sorted(runtime_data.covered_actions)}")
            logger.info(f"  Error actions: {len(runtime_data.error_actions)}")
            logger.info(f"    Error list: {sorted(runtime_data.error_actions)}")
            logger.info(f"  Successful actions: {len(runtime_data.successful_actions)}")
            logger.info(f"    Successful list: {sorted(runtime_data.successful_actions)}")
            logger.info(f"  Runtime coverage score: {coverage_score:.2%}")
            logger.info(f"{'='*60}\n")

            # Store results
            result.overall_success = True
            result.states_explored = sum(
                run.coverage_data.total_evaluations
                for run in runtime_data.simulation_runs
            )

            # Prepare detailed coverage data for each simulation
            simulation_details = []
            for run in runtime_data.simulation_runs:
                simulation_details.append({
                    'run_id': run.run_id,
                    'seed': run.seed,
                    'success': run.success,
                    'states_explored': run.coverage_data.total_evaluations,
                    'actions_covered': len([a for a, (e, n) in run.coverage_data.action_coverage.items() if n > 0]),
                    'error_action': run.error_info.get('error_action') if run.error_info else None
                })

            result.custom_data = {
                'runtime_coverage_score': coverage_score,
                'total_actions': len(runtime_data.all_actions),
                'covered_actions': len(runtime_data.covered_actions),
                'error_actions': len(runtime_data.error_actions),
                'successful_actions': len(runtime_data.successful_actions),
                'all_actions_list': sorted(list(runtime_data.all_actions)),
                'covered_actions_list': sorted(list(runtime_data.covered_actions)),
                'error_actions_list': sorted(list(runtime_data.error_actions)),
                'successful_actions_list': sorted(list(runtime_data.successful_actions)),
                'total_simulations': runtime_data.total_simulations,
                'successful_simulations': runtime_data.successful_simulations,
                'failed_simulations': runtime_data.failed_simulations,
                'simulation_details': simulation_details
            }

        except Exception as e:
            logger.error(f"Runtime coverage evaluation failed: {e}")
            result.overall_success = False
            result.model_checking_error = str(e)

        return result

    def _prepare_spec_files(self, generation_result, spec_file_path, config_file_path,
                           output_dir, task_name, model_name, spec_module):
        """Prepare specification and config files (similar to coverage_evaluator)"""

        if spec_file_path and config_file_path:
            # Use existing files
            logger.info("Using existing .tla and .cfg files")

            spec_name = Path(spec_file_path).stem
            final_spec_path = output_dir / f"{spec_name}.tla"
            final_config_path = output_dir / f"{spec_name}.cfg"

            shutil.copy2(spec_file_path, final_spec_path)
            shutil.copy2(config_file_path, final_config_path)

        elif spec_file_path:
            # Use existing .tla, generate .cfg
            logger.info("Using existing .tla file, generating .cfg file")

            # Copy spec file to output directory for consistency
            spec_name = Path(spec_file_path).stem
            final_spec_path = output_dir / f"{spec_name}.tla"
            shutil.copy2(spec_file_path, final_spec_path)

            final_config_path = self._generate_config_file(
                str(final_spec_path), output_dir, task_name, model_name
            )

        else:
            # Create from GenerationResult
            if not generation_result or not generation_result.success:
                raise ValueError("Generation failed, cannot perform evaluation")

            tla_content = generation_result.generated_text
            if not tla_content.strip():
                raise ValueError("Empty TLA+ specification")

            module_name = spec_module or task_name
            final_spec_path = output_dir / f"{module_name}.tla"

            with open(final_spec_path, 'w', encoding='utf-8') as f:
                f.write(tla_content)

            final_config_path = self._generate_config_file(
                str(final_spec_path), output_dir, task_name, model_name
            )

        return final_spec_path, final_config_path

    def _generate_config_file(self, spec_file_path, output_dir, task_name, model_name):
        """Generate TLC config file"""
        with open(spec_file_path, 'r', encoding='utf-8') as f:
            tla_content = f.read()

        config_generator = ConfigGenerator()
        success, config_content, error = config_generator.generate_config(
            tla_content=tla_content,
            invariants="",
            task_name=task_name,
            model_name=model_name
        )

        if not success:
            raise Exception(f"Config generation failed: {error}")

        spec_name = Path(spec_file_path).stem
        config_file_path = output_dir / f"{spec_name}.cfg"

        with open(config_file_path, 'w', encoding='utf-8') as f:
            f.write(config_content)

        return config_file_path

    def _run_single_simulation(self, spec_path, config_path, output_dir, run_id, seed):
        """Run a single TLC simulation"""

        # Prepare TLC command with simulation mode
        cmd = [
            "java",
            "-cp", str(self.tla_tools_path),
            "tlc2.TLC",
            "-tool",  # Enable tool mode for structured output
            "-coverage", str(self.coverage_interval),  # Enable coverage
            "-simulate", f"num={self.traces_per_simulation}",  # Simulation mode
            "-depth", str(self.simulation_depth),  # Simulation depth
            "-seed", str(seed),  # Random seed
            "-deadlock",  # Disable deadlock checking
            "-config", Path(config_path).name,
            Path(spec_path).name
        ]

        logger.debug(f"Running: {' '.join(cmd)}")

        simulation_run = SimulationRun(run_id=run_id, seed=seed, coverage_data=CoverageData())

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.tlc_timeout,
                cwd=Path(spec_path).parent
            )

            combined_output = result.stdout + result.stderr
            simulation_run.output = combined_output

            # Parse coverage data
            simulation_run.coverage_data = self.parser.parse_tool_output(combined_output)

            # Extract error info to check for behavior trace
            error_info = self._extract_error_info(combined_output)

            # Debug: log what we found
            if error_info["behavior_trace"]:
                logger.info(f"  Simulation {run_id}: Found behavior trace with {len(error_info['behavior_trace'])} actions")
                logger.info(f"    Trace: {error_info['behavior_trace']}")
                logger.info(f"    Error action: {error_info.get('error_action', 'None')}")

            # If there's a behavior trace with actions, consider it an error
            if error_info["behavior_trace"]:
                simulation_run.success = False
                simulation_run.error_info = error_info
            else:
                simulation_run.success = True
                logger.debug(f"  Simulation {run_id}: No behavior trace found")

            # Save output for debugging
            log_file = output_dir / f"simulation_{run_id}_seed_{seed}.log"
            with open(log_file, 'w') as f:
                f.write(f"Command: {' '.join(cmd)}\n")
                f.write(f"Exit code: {result.returncode}\n")
                f.write(f"Seed: {seed}\n")
                f.write(f"Success: {simulation_run.success}\n")
                f.write(f"\n{combined_output}\n")

        except subprocess.TimeoutExpired as e:
            logger.warning(f"Simulation {run_id} timed out")
            # Try to parse partial output
            if hasattr(e, 'stdout') and hasattr(e, 'stderr'):
                stdout_str = e.stdout.decode('utf-8') if isinstance(e.stdout, bytes) else (e.stdout or "")
                stderr_str = e.stderr.decode('utf-8') if isinstance(e.stderr, bytes) else (e.stderr or "")
                combined_output = stdout_str + stderr_str
                simulation_run.output = combined_output
                simulation_run.coverage_data = self.parser.parse_tool_output(combined_output)
                simulation_run.success = True  # Timeout is not an error

        except Exception as e:
            logger.error(f"Simulation {run_id} failed: {e}")
            simulation_run.success = False
            simulation_run.error_info = {"error": str(e)}

        return simulation_run

    def _aggregate_coverage(self, runtime_data: RuntimeCoverageData, simulation_run: SimulationRun):
        """Aggregate coverage data from a simulation run"""

        coverage = simulation_run.coverage_data

        # Collect all actions from the specification
        for action_name in coverage.action_coverage.keys():
            runtime_data.all_actions.add(action_name)

        # Collect covered actions (those that produced new states)
        for action_name, (evaluations, new_states) in coverage.action_coverage.items():
            if new_states > 0:  # Changed from evaluations > 0
                runtime_data.covered_actions.add(action_name)
                logger.debug(f"    Action {action_name} covered: {evaluations} evals, {new_states} states")

    def _extract_error_info(self, output: str) -> Dict[str, Any]:
        """Extract error information from TLC output - mainly looking for behavior trace"""

        error_info = {
            "error_action": None,
            "behavior_trace": []
        }

        lines = output.split('\n')

        # Look for lines that match "N: <Something"
        behavior_trace = []
        for i, line in enumerate(lines):
            # Simple pattern: number, colon, space, angle bracket
            if re.match(r'^\d+:\s*<', line.strip()):
                # Extract action name - everything between < and space/parenthesis
                match = re.search(r'<([^<>\s\(]+)', line)
                if match:
                    action = match.group(1)
                    behavior_trace.append(action)
                    logger.debug(f"    Found state action: {action}")

        # Copy found trace to error_info
        error_info["behavior_trace"] = behavior_trace

        # The last action in the trace is likely the error action
        if behavior_trace:
            error_info["error_action"] = behavior_trace[-1]
            logger.debug(f"  Found behavior trace with {len(behavior_trace)} actions: {behavior_trace}")
            logger.debug(f"  Identified error action: {error_info['error_action']}")

        return error_info

    def _process_error(self, runtime_data: RuntimeCoverageData, simulation_run: SimulationRun):
        """Process error information and identify error actions"""

        error_info = simulation_run.error_info

        if error_info.get("error_action"):
            # Found error action from behavior trace
            error_action = error_info["error_action"]
            runtime_data.error_actions.add(error_action)
            logger.info(f"  Found error action from behavior trace: {error_action}")

        elif error_info.get("behavior_trace"):
            # Has trace but couldn't identify specific action
            logger.warning(f"  Found behavior trace but couldn't identify error action")
            logger.warning(f"  Trace: {error_info['behavior_trace']}")

    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "runtime_coverage"


def create_runtime_coverage_evaluator(
    num_simulations: int = 20,
    simulation_depth: int = 50,
    traces_per_simulation: int = 50,
    tlc_timeout: int = 30,
    coverage_interval: int = 1
) -> RuntimeCoverageEvaluator:
    """
    Factory function to create a runtime coverage evaluator.

    Args:
        num_simulations: Number of simulation runs
        simulation_depth: Maximum depth for each simulation trace
        traces_per_simulation: Number of traces per simulation
        tlc_timeout: Timeout for each TLC simulation in seconds
        coverage_interval: Interval for coverage statistics in minutes

    Returns:
        RuntimeCoverageEvaluator instance
    """
    return RuntimeCoverageEvaluator(
        num_simulations=num_simulations,
        simulation_depth=simulation_depth,
        traces_per_simulation=traces_per_simulation,
        tlc_timeout=tlc_timeout,
        coverage_interval=coverage_interval
    )