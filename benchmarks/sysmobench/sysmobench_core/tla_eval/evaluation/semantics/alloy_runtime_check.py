"""Alloy runtime evaluator that executes all run/check commands."""

import json
import logging
import time
from pathlib import Path
from typing import Optional

from ...models.base import GenerationResult
from ...utils.output_manager import get_output_manager
from ..base.evaluator import BaseEvaluator
from ..base.result_types import SemanticEvaluationResult
from ...core.verification.alloy_runtime_executor import AlloyRuntimeExecutor

logger = logging.getLogger(__name__)


class AlloyRuntimeCheckEvaluator(BaseEvaluator):
    """
    Evaluator for Alloy runtime checking (executing run/check commands).
    """

    def __init__(self, validation_timeout: int = 60):
        """
        Initialize Alloy runtime check evaluator.

        Args:
            validation_timeout: Timeout for runtime checking in seconds
        """
        super().__init__(timeout=validation_timeout)
        self.runtime_executor = AlloyRuntimeExecutor(timeout=validation_timeout)

    def evaluate(self,
                generation_result: GenerationResult,
                task_name: str,
                method_name: str,
                model_name: str,
                spec_module: str = None,
                spec_file_path: Optional[str] = None,
                config_file_path: Optional[str] = None) -> SemanticEvaluationResult:
        """
        Evaluate Alloy specification runtime checking.

        Args:
            generation_result: Result from Alloy generation
            task_name: Name of the task
            method_name: Name of the generation method
            model_name: Name of the model used
            spec_module: Not used for Alloy
            spec_file_path: Optional path to existing .als file
            config_file_path: Not used for Alloy

        Returns:
            SemanticEvaluationResult with runtime checking metrics
        """
        logger.info(f"Evaluating Alloy runtime: {task_name}/{method_name}/{model_name}")

        # Create output directory
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="runtime_check",
            task=task_name,
            method=method_name,
            model=model_name,
            language="alloy"
        )
        logger.info(f"Using output directory: {output_dir}")

        # Create evaluation result
        eval_result = SemanticEvaluationResult(task_name, method_name, model_name)

        # Get Alloy content
        if spec_file_path and Path(spec_file_path).exists():
            logger.info(f"Using existing spec file: {spec_file_path}")
            alloy_file = Path(spec_file_path)
            eval_result.specification_file = str(alloy_file)
        elif generation_result and generation_result.generated_text:
            logger.info("Using generated Alloy specification")
            # Save to output directory
            alloy_file = output_dir / f"{task_name}.als"
            alloy_file.write_text(generation_result.generated_text, encoding='utf-8')
            eval_result.specification_file = str(alloy_file)
        else:
            logger.error("No valid spec file or generation result provided")
            eval_result.model_checking_successful = False
            eval_result.model_checking_error = "No specification provided"
            eval_result.overall_success = False
            return eval_result

        # Execute runtime checking
        logger.info("Starting Alloy runtime checking")
        start_time = time.time()

        runtime_result = self.runtime_executor.run(alloy_file)

        eval_result.model_checking_time = time.time() - start_time
        eval_result.model_checking_successful = runtime_result['success']

        if runtime_result['success']:
            eval_result.states_explored = runtime_result.get('total_commands', 0)
            eval_result.model_checking_error = None

            # Store command results in custom_data
            eval_result.custom_data = {
                'total_commands': runtime_result.get('total_commands', 0),
                'successful_commands': runtime_result.get('successful_commands', 0),
                'failed_commands': runtime_result.get('failed_commands', 0),
                'command_results': runtime_result.get('commands', [])
            }

            logger.info(f"Runtime check passed: {runtime_result['successful_commands']}/{runtime_result['total_commands']} commands succeeded")
        else:
            eval_result.model_checking_error = runtime_result.get('error', 'Unknown error')
            logger.error(f"Runtime check failed: {eval_result.model_checking_error}")

        eval_result.overall_success = eval_result.model_checking_successful

        # Save results
        results_file = output_dir / "evaluation_result.json"
        try:
            with open(results_file, 'w', encoding='utf-8') as f:
                json.dump(eval_result.to_dict(), f, indent=2)
            logger.info(f"Saved evaluation results to {results_file}")
        except Exception as e:
            logger.warning(f"Failed to save results: {e}")

        return eval_result

    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "alloy_runtime"
