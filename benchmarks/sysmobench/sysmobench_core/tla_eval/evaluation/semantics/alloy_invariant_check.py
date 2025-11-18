"""
Alloy Invariant Evaluator: Phase 3/4 evaluation for Alloy specifications.

This evaluator implements the invariant verification phase:
1. Load expert-written invariant templates
2. Translate templates to specific Alloy specification (using Claude)
3. Run Alloy model checking for each invariant (static composition)
4. Report detailed results

Mirrors the TLA+ ManualInvariantEvaluator design.
"""

import json
import logging
import time
from pathlib import Path
from typing import Dict, Any, List, Optional
from dataclasses import dataclass

from ...models.base import GenerationResult
from ...utils.output_manager import get_output_manager
from ..base.evaluator import BaseEvaluator
from ..base.result_types import SemanticEvaluationResult
from ...core.verification.alloy_runtime_executor import AlloyRuntimeExecutor

# Import the new translator
from .alloy_invariant_translator import (
    AlloyInvariantTemplateLoader,
    AlloyInvariantTranslator,
    AlloyInvariantTemplate
)

logger = logging.getLogger(__name__)


@dataclass
class AlloyInvariantTestResult:
    """Result of testing a single Alloy invariant"""
    name: str
    success: bool
    translated_invariant: str
    error_message: Optional[str] = None
    exec_time_seconds: float = 0.0
    alloy_output: str = ""


class AlloyInvariantCheckEvaluator(BaseEvaluator):
    """
    Alloy Invariant Evaluator: Phase 3/4 evaluation for Alloy specifications.

    This evaluator implements invariant verification:
    1. Load expert-written invariant templates
    2. Translate templates to specific Alloy specification (using Claude)
    3. Run Alloy checking for each invariant (using static composition)
    4. Report detailed results
    """

    def __init__(self, validation_timeout: int = 60, templates_dir: str = "data/alloy_invariant_templates"):
        """
        Initialize Alloy invariant evaluator.

        Args:
            validation_timeout: Timeout for Alloy execution in seconds
            templates_dir: Directory containing invariant templates
        """
        super().__init__(timeout=validation_timeout)
        self.template_loader = AlloyInvariantTemplateLoader(templates_dir)
        self.translator = AlloyInvariantTranslator()
        self.runtime_executor = AlloyRuntimeExecutor(timeout=validation_timeout)

    def evaluate(self,
                generation_result: GenerationResult,
                task_name: str,
                method_name: str,
                model_name: str,
                spec_module: Optional[str] = None,
                spec_file_path: Optional[str] = None,
                config_file_path: Optional[str] = None) -> SemanticEvaluationResult:
        """
        Evaluate an Alloy specification using invariant testing.

        This method supports multiple modes:
        1. Composite mode: Reuse spec file from runtime check
        2. Standalone mode: Generate spec file independently

        Args:
            generation_result: GenerationResult containing the Alloy specification
            task_name: Name of the task
            method_name: Name of the generation method
            model_name: Name of the model used
            spec_module: Optional Alloy module name (not used for Alloy, kept for compatibility)
            spec_file_path: Optional path to existing .als file (composite mode)
            config_file_path: Not used for Alloy (kept for API compatibility)

        Returns:
            SemanticEvaluationResult with invariant testing results
        """
        logger.info(f"Alloy invariant evaluation: {task_name}/{method_name}/{model_name}")

        # Create structured output directory
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="invariant_verification",
            task=task_name,
            method=method_name,
            model=model_name,
            language="alloy"
        )
        logger.info(f"Using output directory: {output_dir}")

        # Create evaluation result
        result = SemanticEvaluationResult(task_name, method_name, model_name)

        # Set generation time from the generation result metadata
        if hasattr(generation_result, 'metadata') and 'latency_seconds' in generation_result.metadata:
            result.generation_time = generation_result.metadata['latency_seconds']

        if not generation_result.success:
            result.invariant_generation_error = "Generation failed"
            result.overall_success = False
            return result

        # Determine working mode and prepare specification file
        if spec_file_path and Path(spec_file_path).exists():
            # Composite mode: Reuse existing spec file but copy to output directory
            logger.info(f"✓ Composite mode: Reusing existing spec file from runtime check: {spec_file_path}")

            # Read content from runtime check file
            with open(spec_file_path, 'r', encoding='utf-8') as f:
                alloy_content = f.read()

            # Create copy in invariant verification output directory
            spec_file = output_dir / f"{task_name}.als"
            with open(spec_file, 'w', encoding='utf-8') as f:
                f.write(alloy_content)
            result.specification_file = str(spec_file)
            logger.info(f"✓ Copied spec file to invariant verification directory: {spec_file}")
        else:
            # Standalone mode: Create new spec file
            logger.info("✓ Standalone mode: Creating new spec file")
            spec_file = output_dir / f"{task_name}.als"
            with open(spec_file, 'w', encoding='utf-8') as f:
                f.write(generation_result.generated_text)
            result.specification_file = str(spec_file)
            alloy_content = generation_result.generated_text

        try:
            # Step 1: Load invariant templates
            logger.info("Step 1: Loading invariant templates...")
            templates = self.template_loader.load_task_invariants(task_name)

            # Step 2: Translate all invariants in one LLM call
            logger.info("Step 2: Translating invariants to specification...")
            translation_start = time.time()
            success, translated_invariants, error = self.translator.translate_all_invariants(
                templates, alloy_content, task_name, model_name
            )

            result.invariant_generation_time = time.time() - translation_start
            result.invariant_generation_successful = success

            if not success:
                result.invariant_generation_error = error
                result.overall_success = False
                return result

            logger.info(f"Successfully translated {len(translated_invariants)} invariants")

            # Step 3: Test each invariant individually
            logger.info("Step 3: Testing invariants with Alloy...")
            invariant_results = []

            for i, template in enumerate(templates, 1):
                if template.name not in translated_invariants:
                    logger.warning(f"Invariant {template.name} was not translated, skipping")
                    continue

                logger.info(f"=== TESTING INVARIANT {i}/{len(templates)}: {template.name} ===")
                invariant_test_result = self._test_single_invariant(
                    template, translated_invariants[template.name],
                    alloy_content, output_dir, task_name
                )

                # Print detailed results for each invariant test
                logger.info(f"INVARIANT {i} RESULT: {template.name}")
                logger.info(f"  Success: {invariant_test_result.success}")
                logger.info(f"  Execution time: {invariant_test_result.exec_time_seconds:.2f}s")
                if invariant_test_result.error_message:
                    logger.info(f"  Error: {invariant_test_result.error_message}")
                logger.info(f"  Translated invariant: {invariant_test_result.translated_invariant[:200]}...")
                logger.info("")

                invariant_results.append(invariant_test_result)

            # Step 4: Aggregate results
            result.model_checking_successful = any(r.success for r in invariant_results)
            result.model_checking_time = sum(r.exec_time_seconds for r in invariant_results)

            # Set overall success - all invariants must pass
            passed_count = sum(1 for r in invariant_results if r.success)
            total_count = len(invariant_results)

            result.overall_success = (
                result.invariant_generation_successful and
                result.model_checking_successful and
                total_count > 0 and
                passed_count == total_count  # All invariants must pass
            )

            # Store detailed results
            result.custom_data = {
                "invariant_results": [
                    {
                        "name": r.name,
                        "success": r.success,
                        "exec_time_seconds": r.exec_time_seconds,
                        "error_message": r.error_message
                    }
                    for r in invariant_results
                ],
                "total_invariants": len(templates),
                "translated_invariants": len(translated_invariants),
                "passed_invariants": sum(1 for r in invariant_results if r.success),
                "failed_invariants": sum(1 for r in invariant_results if not r.success)
            }

            # Log detailed summary
            passed = result.custom_data["passed_invariants"]
            total = len(invariant_results)

            logger.info("=== ALLOY INVARIANT VERIFICATION FINAL SUMMARY ===")
            logger.info(f"Total invariants tested: {total}")
            logger.info(f"Passed invariants: {passed}")
            logger.info(f"Failed invariants: {total - passed}")

            # List all results by name
            for i, inv_result in enumerate(invariant_results, 1):
                status = "✓ PASS" if inv_result.success else "✗ FAIL"
                logger.info(f"  {i}. {inv_result.name}: {status}")

            # Show final judgment logic
            logger.info(f"Invariant generation successful: {result.invariant_generation_successful}")
            logger.info(f"Model checking successful: {result.model_checking_successful}")
            logger.info(f"All invariants passed: {passed == total}")
            logger.info(f"Overall success: {result.overall_success}")
            logger.info(f"Alloy invariant testing: {passed}/{total} invariants passed")

            # Save results to JSON file
            results_file = output_dir / "evaluation_result.json"
            try:
                with open(results_file, "w", encoding="utf-8") as handle:
                    json.dump(result.to_dict(), handle, indent=2)
            except Exception as exc:
                logger.warning(f"Failed to save invariant evaluation results: {exc}")

            return result

        except Exception as e:
            logger.error(f"Alloy invariant evaluation failed: {e}")
            result.invariant_generation_error = str(e)
            result.overall_success = False
            return result

    def _test_single_invariant(self,
                              template: AlloyInvariantTemplate,
                              translated_invariant: str,
                              alloy_content: str,
                              output_dir: Path,
                              task_name: str) -> AlloyInvariantTestResult:
        """Test a single invariant using Alloy"""

        logger.debug(f"Testing invariant: {template.name}")

        try:
            # Create directory for this invariant
            invariant_dir = output_dir / template.name
            invariant_dir.mkdir(exist_ok=True)

            # Create modified Alloy spec with the invariant
            # Simply append the translated invariant to the base spec
            modified_spec = alloy_content + "\n\n// ---- Invariant: " + template.name + " ----\n" + translated_invariant

            # Save modified spec
            modified_spec_file = invariant_dir / f"{task_name}_{template.name}.als"
            with open(modified_spec_file, 'w', encoding='utf-8') as f:
                f.write(modified_spec)

            # Run Alloy
            start_time = time.time()
            runtime_result = self.runtime_executor.run(modified_spec_file)
            exec_time = time.time() - start_time

            # Parse Alloy results
            # runtime_result contains: {"success": bool, "commands": [...], "error": str}
            commands = runtime_result.get("commands", [])

            # Find the check command for this invariant
            invariant_cmd = None
            if commands:
                # Look for a check command (type == "check")
                invariant_cmd = next(
                    (cmd for cmd in commands if str(cmd.get("type", "")).lower() == "check"),
                    commands[0]  # Fallback to first command
                )

            if not invariant_cmd:
                return AlloyInvariantTestResult(
                    name=template.name,
                    success=False,
                    translated_invariant=translated_invariant,
                    error_message=runtime_result.get("error", "No check command executed"),
                    exec_time_seconds=exec_time,
                    alloy_output=str(runtime_result)
                )

            # Check if the result is PASS
            result_str = str(invariant_cmd.get("result", ""))
            success = result_str.upper().startswith("PASS")

            return AlloyInvariantTestResult(
                name=template.name,
                success=success,
                translated_invariant=translated_invariant,
                exec_time_seconds=exec_time,
                alloy_output=str(invariant_cmd),
                error_message=None if success else f"Check failed: {result_str}"
            )

        except Exception as e:
            return AlloyInvariantTestResult(
                name=template.name,
                success=False,
                translated_invariant=translated_invariant,
                error_message=f"Testing failed: {str(e)}",
                exec_time_seconds=0.0
            )

    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "alloy_invariant_verification"


# Convenience function for backward compatibility
def create_alloy_invariant_evaluator(validation_timeout: int = 60,
                                     templates_dir: str = "data/alloy_invariant_templates") -> AlloyInvariantCheckEvaluator:
    """
    Factory function to create an Alloy invariant evaluator.

    Args:
        validation_timeout: Timeout for Alloy execution in seconds
        templates_dir: Directory containing invariant templates

    Returns:
        AlloyInvariantCheckEvaluator instance
    """
    return AlloyInvariantCheckEvaluator(validation_timeout=validation_timeout, templates_dir=templates_dir)
