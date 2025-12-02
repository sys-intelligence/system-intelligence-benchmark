"""
PAT Compilation Check Evaluator: Syntax-level evaluation for PAT/CSP specifications.

This evaluator checks whether generated PAT/CSP specifications can be validated
using PAT Console.
"""

import logging
import time
from pathlib import Path
from typing import Optional

from ...core.verification.pat_validator import PATValidator, ValidationResult
from ...models.base import GenerationResult
from ...utils.output_manager import get_output_manager
from ..base.evaluator import BaseEvaluator
from ..base.result_types import SyntaxEvaluationResult

logger = logging.getLogger(__name__)


class PATCompilationCheckEvaluator(BaseEvaluator):
    """
    Evaluator for PAT specification compilation checking.

    This evaluator checks whether generated PAT/CSP specifications pass
    syntax validation using PAT Console.
    """

    def __init__(self, validation_timeout: int = 30):
        """
        Initialize PAT compilation check evaluator.

        Args:
            validation_timeout: Timeout for validation in seconds
        """
        super().__init__(timeout=validation_timeout)
        self.validator = PATValidator(timeout=validation_timeout)

    def evaluate(self,
                 generation_result: GenerationResult,
                 task_name: str,
                 method_name: str,
                 model_name: str,
                 spec_module: str = None,
                 spec_file_path: Optional[str] = None,
                 config_file_path: Optional[str] = None) -> SyntaxEvaluationResult:
        """
        Evaluate a single generation result for compilation success.

        Args:
            generation_result: Result from PAT generation
            task_name: Name of the task
            method_name: Name of the generation method
            model_name: Name of the model used
            spec_module: Optional PAT module name (not used for PAT)
            spec_file_path: Optional path to existing .csp file (use instead of generation_result)
            config_file_path: Not applicable for PAT (kept for interface compatibility)

        Returns:
            SyntaxEvaluationResult with evaluation metrics
        """
        logger.info(f"Evaluating PAT compilation: {task_name}/{method_name}/{model_name}")

        # Create structured output directory
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="compilation_check",
            task=task_name,
            method=method_name,
            model=model_name,
            language="pat"
        )
        logger.info(f"Using output directory: {output_dir}")

        # Create evaluation result
        eval_result = SyntaxEvaluationResult(task_name, method_name, model_name)
        self._set_generation_result(eval_result, generation_result)

        # Determine input source and get PAT content
        if spec_file_path and Path(spec_file_path).exists():
            # Use existing spec file
            logger.info(f"Using existing spec file: {spec_file_path}")
            try:
                with open(spec_file_path, 'r', encoding='utf-8') as f:
                    pat_content = f.read()
            except Exception as e:
                logger.error(f"Failed to read spec file: {e}")
                validation_result = ValidationResult(
                    success=False,
                    output=f"Failed to read spec file: {e}",
                    syntax_errors=[f"Cannot read spec file: {e}"],
                    semantic_errors=[],
                    compilation_time=0.0
                )
                self._set_validation_result(eval_result, validation_result)
                return eval_result

        elif generation_result and getattr(generation_result, "generated_text", None):
            # Use generated content
            logger.info("Using generated PAT specification")
            pat_content = generation_result.generated_text

        else:
            # No valid input
            logger.error("No valid spec file or generation result provided")
            validation_result = ValidationResult(
                success=False,
                output="No specification content available",
                syntax_errors=["No specification provided"],
                semantic_errors=[],
                compilation_time=0.0
            )
            self._set_validation_result(eval_result, validation_result)
            return eval_result

        # Save specification to output directory
        spec_output_path = output_dir / f"{task_name}.csp"
        try:
            with open(spec_output_path, 'w', encoding='utf-8') as f:
                f.write(pat_content)
            logger.info(f"Saved PAT specification to {spec_output_path}")
        except Exception as e:
            logger.warning(f"Failed to save specification: {e}")

        # Perform validation
        logger.info("Starting PAT validation")
        validation_result = self.validator.validate(pat_content, output_dir)

        # Set validation result
        self._set_validation_result(eval_result, validation_result)

        # Save detailed results
        results_file = output_dir / "evaluation_result.json"
        try:
            import json
            with open(results_file, 'w', encoding='utf-8') as f:
                json.dump(eval_result.to_dict(), f, indent=2)
            logger.info(f"Saved evaluation results to {results_file}")
        except Exception as e:
            logger.warning(f"Failed to save results: {e}")

        return eval_result

    def _set_generation_result(self, eval_result: SyntaxEvaluationResult, generation_result: GenerationResult):
        """Set generation-related fields in evaluation result"""
        if generation_result:
            eval_result.generation_successful = generation_result.success
            # Extract generation time from metadata
            eval_result.generation_time = generation_result.metadata.get('latency_seconds', 0.0)
            eval_result.generation_error = generation_result.error_message if not generation_result.success else None
            eval_result.generated_specification = generation_result.generated_text
        else:
            eval_result.generation_successful = True  # Using existing file
            eval_result.generation_time = 0.0

    def _set_validation_result(self, eval_result: SyntaxEvaluationResult, validation_result: ValidationResult):
        """Set validation-related fields in evaluation result"""
        eval_result.compilation_successful = validation_result.success
        eval_result.compilation_time = validation_result.compilation_time
        eval_result.syntax_errors = validation_result.syntax_errors
        eval_result.semantic_errors = validation_result.semantic_errors
        eval_result.compilation_output = validation_result.output

        # Align with other evaluators so downstream stats/reporting work
        eval_result.compilation_errors = (
            list(validation_result.syntax_errors)
            + list(validation_result.semantic_errors)
        )

        # Overall success requires both generation and compilation to succeed
        eval_result.overall_success = (
            eval_result.generation_successful and
            eval_result.compilation_successful
        )

        logger.info(
            f"Evaluation result: generation={'✓' if eval_result.generation_successful else '✗'}, "
            f"compilation={'✓' if eval_result.compilation_successful else '✗'}, "
            f"overall={'✓' if eval_result.overall_success else '✗'}"
        )

    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "pat_syntax"
