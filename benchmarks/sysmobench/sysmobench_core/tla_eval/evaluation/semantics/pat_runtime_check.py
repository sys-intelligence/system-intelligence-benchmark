"""PAT runtime evaluator that executes model checking on CSP specifications."""

import json
import logging
import time
from pathlib import Path
from typing import Optional

from ...models.base import GenerationResult
from ...utils.output_manager import get_output_manager
from ..base.evaluator import BaseEvaluator
from ..base.result_types import SemanticEvaluationResult
from ...core.verification.pat_runtime_executor import PATRuntimeExecutor

logger = logging.getLogger(__name__)


class PATRuntimeCheckEvaluator(BaseEvaluator):
    """
    Evaluator for PAT runtime checking (executing model checking on CSP specifications).

    This evaluator runs PAT Console to verify all assertions in the specification
    and reports detailed results including states explored, verification time, and
    any counterexamples found.
    """

    def __init__(self, validation_timeout: int = 60):
        """
        Initialize PAT runtime check evaluator.

        Args:
            validation_timeout: Timeout for runtime checking in seconds
        """
        super().__init__(timeout=validation_timeout)
        self.runtime_executor = PATRuntimeExecutor(timeout=validation_timeout)
        logger.info(f"PATRuntimeCheckEvaluator initialized with {validation_timeout}s timeout")

    def evaluate(self,
                generation_result: GenerationResult,
                task_name: str,
                method_name: str,
                model_name: str,
                spec_module: str = None,
                spec_file_path: Optional[str] = None,
                config_file_path: Optional[str] = None) -> SemanticEvaluationResult:
        """
        Evaluate PAT specification runtime checking.

        Args:
            generation_result: Result from PAT generation
            task_name: Name of the task
            method_name: Name of the generation method
            model_name: Name of the model used
            spec_module: Not used for PAT
            spec_file_path: Optional path to existing .csp file
            config_file_path: Not used for PAT (assertions are in the spec file)

        Returns:
            SemanticEvaluationResult with runtime checking metrics
        """
        logger.info(f"Evaluating PAT runtime: {task_name}/{method_name}/{model_name}")

        # Create output directory
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="runtime_check",
            task=task_name,
            method=method_name,
            model=model_name,
            language="pat"
        )
        logger.info(f"Using output directory: {output_dir}")

        # Create evaluation result
        eval_result = SemanticEvaluationResult(task_name, method_name, model_name)

        # Get CSP content
        if spec_file_path and Path(spec_file_path).exists():
            logger.info(f"Using existing spec file: {spec_file_path}")
            csp_file = Path(spec_file_path)
            eval_result.specification_file = str(csp_file)
        elif generation_result and generation_result.generated_text:
            logger.info("Using generated CSP specification")
            # Save to output directory
            csp_file = output_dir / f"{task_name}.csp"
            csp_file.write_text(generation_result.generated_text, encoding='utf-8')
            eval_result.specification_file = str(csp_file)
        else:
            logger.error("No valid spec file or generation result provided")
            eval_result.model_checking_successful = False
            eval_result.model_checking_error = "No specification provided"
            eval_result.overall_success = False
            return eval_result

        # Execute runtime checking
        logger.info("Starting PAT runtime checking")
        start_time = time.time()

        runtime_result = self.runtime_executor.run(csp_file)

        eval_result.model_checking_time = time.time() - start_time
        eval_result.model_checking_successful = runtime_result['success']

        if runtime_result['success']:
            # Success: extract metrics
            eval_result.states_explored = sum(
                a.get('visited_states', 0) for a in runtime_result.get('assertions', [])
            )
            eval_result.model_checking_output = self._format_runtime_output(runtime_result)

            logger.info(
                f"PAT runtime check passed: {runtime_result['passed_assertions']}/{runtime_result['total_assertions']} assertions, "
                f"{eval_result.states_explored} states explored"
            )

            # Overall success
            eval_result.overall_success = True

        else:
            # Failure: extract error information
            error_msg = runtime_result.get('error', 'Unknown error')
            eval_result.model_checking_error = error_msg
            eval_result.model_checking_output = error_msg

            # Extract counterexamples if available
            counterexamples = []
            for assertion in runtime_result.get('assertions', []):
                if assertion.get('result') == 'INVALID':
                    ce_info = {
                        'assertion': assertion.get('name', 'Unknown'),
                        'counterexample': assertion.get('counterexample', 'No details available')
                    }
                    counterexamples.append(ce_info)

            if counterexamples:
                eval_result.counterexamples = counterexamples
                logger.warning(f"Found {len(counterexamples)} counterexamples")

            logger.error(f"PAT runtime check failed: {error_msg}")
            eval_result.overall_success = False

        # Save detailed results to JSON
        self._save_detailed_results(output_dir, task_name, runtime_result, eval_result)

        return eval_result

    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "pat_runtime"

    def _format_runtime_output(self, runtime_result: dict) -> str:
        """
        Format runtime result into a human-readable string.

        Args:
            runtime_result: Parsed runtime result from PATRuntimeExecutor

        Returns:
            Formatted string
        """
        lines = [
            f"PAT Runtime Check Results",
            f"=" * 60,
            f"Total Assertions: {runtime_result['total_assertions']}",
            f"Passed: {runtime_result['passed_assertions']}",
            f"Failed: {runtime_result['failed_assertions']}",
            f"Total Time: {runtime_result['total_time']:.4f}s",
            ""
        ]

        for i, assertion in enumerate(runtime_result.get('assertions', []), 1):
            lines.append(f"Assertion {i}: {assertion.get('name', 'Unknown')}")
            lines.append(f"  Result: {assertion.get('result', 'UNKNOWN')}")
            lines.append(f"  Visited States: {assertion.get('visited_states', 0)}")
            lines.append(f"  Transitions: {assertion.get('transitions', 0)}")
            lines.append(f"  Time: {assertion.get('time_used', 0.0):.4f}s")
            if 'memory_used' in assertion:
                lines.append(f"  Memory: {assertion['memory_used']}")
            if assertion.get('result') == 'INVALID' and 'counterexample' in assertion:
                lines.append(f"  Counterexample: {assertion['counterexample'][:100]}...")
            lines.append("")

        return "\n".join(lines)

    def _save_detailed_results(self, output_dir: Path, task_name: str,
                              runtime_result: dict, eval_result: SemanticEvaluationResult):
        """
        Save detailed runtime results to JSON file.

        Args:
            output_dir: Output directory
            task_name: Task name
            runtime_result: Runtime result from executor
            eval_result: Evaluation result
        """
        try:
            results_file = output_dir / f"{task_name}_runtime_results.json"

            detailed_results = {
                "task_name": task_name,
                "success": runtime_result['success'],
                "total_assertions": runtime_result.get('total_assertions', 0),
                "passed_assertions": runtime_result.get('passed_assertions', 0),
                "failed_assertions": runtime_result.get('failed_assertions', 0),
                "total_time": runtime_result.get('total_time', 0.0),
                "states_explored": eval_result.states_explored,
                "assertions": runtime_result.get('assertions', []),
                "error": runtime_result.get('error'),
                "specification_file": eval_result.specification_file
            }

            with open(results_file, 'w', encoding='utf-8') as f:
                json.dump(detailed_results, f, indent=2, ensure_ascii=False)

            logger.info(f"Saved detailed results to: {results_file}")

        except Exception as e:
            logger.warning(f"Failed to save detailed results: {e}")

    def batch_evaluate(self, generation_results: list, task_name: str,
                      method_name: str, model_name: str) -> dict:
        """
        Evaluate multiple PAT specifications.

        Args:
            generation_results: List of generation results
            task_name: Task name
            method_name: Method name
            model_name: Model name

        Returns:
            Summary dictionary
        """
        results = []

        for i, gen_result in enumerate(generation_results, 1):
            logger.info(f"Evaluating {i}/{len(generation_results)}")
            eval_result = self.evaluate(gen_result, task_name, method_name, model_name)
            results.append(eval_result)

        # Generate summary
        return self._generate_summary(results)

    def _generate_summary(self, results: list) -> dict:
        """
        Generate summary statistics from evaluation results.

        Args:
            results: List of SemanticEvaluationResult

        Returns:
            Summary dictionary
        """
        total = len(results)
        successful = sum(1 for r in results if r.model_checking_successful)

        # Time statistics
        checking_times = [r.model_checking_time for r in results if r.model_checking_time > 0]

        # States statistics
        states_explored = [r.states_explored for r in results if r.states_explored > 0]

        summary = {
            "total_evaluations": total,
            "successful_checks": successful,
            "failed_checks": total - successful,
            "success_rate": successful / total if total > 0 else 0.0,
            "timing": {
                "total_checking_time": sum(checking_times),
                "avg_checking_time": sum(checking_times) / len(checking_times) if checking_times else 0.0,
                "min_checking_time": min(checking_times) if checking_times else 0.0,
                "max_checking_time": max(checking_times) if checking_times else 0.0
            },
            "exploration": {
                "total_states": sum(states_explored),
                "avg_states_per_check": sum(states_explored) / len(states_explored) if states_explored else 0.0,
                "max_states": max(states_explored) if states_explored else 0
            }
        }

        return summary
