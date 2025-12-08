"""
PAT Invariant Evaluator: Phase 4 evaluation for PAT/CSP specifications.

This evaluator implements invariant verification:
1. Load expert-written invariant templates
2. Translate templates to specific CSP assertions (using Claude)
3. Run PAT model checking for each invariant (static composition)
4. Report detailed results

Mirrors the TLA+ ManualInvariantEvaluator and Alloy AlloyInvariantCheckEvaluator design.
"""

import json
import logging
import re
import time
from pathlib import Path
from typing import Dict, Any, List, Optional
from dataclasses import dataclass

from ...models.base import GenerationResult
from ...utils.output_manager import get_output_manager
from ..base.evaluator import BaseEvaluator
from ..base.result_types import SemanticEvaluationResult
from ...core.verification.pat_runtime_executor import PATRuntimeExecutor
from ...core.verification.pat_invariant_loader import (
    PATInvariantTemplateLoader,
    PATInvariantTemplate
)
from ...core.verification.pat_invariant_translator import PATInvariantTranslator

logger = logging.getLogger(__name__)


@dataclass
class PATInvariantTestResult:
    """Result of testing a single PAT invariant"""
    name: str
    success: bool
    translated_invariant: str
    error_message: Optional[str] = None
    visited_states: int = 0
    verification_time: float = 0.0
    pat_output: str = ""


class PATInvariantCheckEvaluator(BaseEvaluator):
    """
    PAT Invariant Evaluator: Phase 4 evaluation for PAT/CSP specifications.

    This evaluator implements invariant verification by:
    1. Loading expert-written invariant templates
    2. Translating templates to specific CSP assertions
    3. Running PAT checking for each invariant using static composition
    4. Reporting detailed results
    """

    def __init__(
        self,
        validation_timeout: int = 60,
        templates_dir: str = "data/pat_invariant_templates"
    ):
        """
        Initialize PAT invariant evaluator.

        Args:
            validation_timeout: Timeout for PAT execution in seconds
            templates_dir: Directory containing invariant templates
        """
        super().__init__(timeout=validation_timeout)
        self.template_loader = PATInvariantTemplateLoader(templates_dir)
        self.translator = PATInvariantTranslator()
        self.runtime_executor = PATRuntimeExecutor(timeout=validation_timeout)
        logger.info(
            f"PATInvariantCheckEvaluator initialized with {validation_timeout}s timeout"
        )

    def evaluate(
        self,
        generation_result: GenerationResult,
        task_name: str,
        method_name: str,
        model_name: str,
        spec_module: Optional[str] = None,
        spec_file_path: Optional[str] = None,
        config_file_path: Optional[str] = None
    ) -> SemanticEvaluationResult:
        """
        Evaluate a PAT specification using invariant testing.

        This method supports multiple modes:
        1. Composite mode: Reuse spec file from runtime check
        2. Standalone mode: Generate spec file independently

        Args:
            generation_result: GenerationResult containing the CSP specification
            task_name: Name of the task
            method_name: Name of the generation method
            model_name: Name of the model used
            spec_module: Not used for PAT (kept for API compatibility)
            spec_file_path: Optional path to existing .csp file (composite mode)
            config_file_path: Not used for PAT (kept for API compatibility)

        Returns:
            SemanticEvaluationResult with invariant testing results
        """
        logger.info(f"PAT invariant evaluation: {task_name}/{method_name}/{model_name}")

        # Create structured output directory
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="invariant_verification",
            task=task_name,
            method=method_name,
            model=model_name,
            language="pat"
        )
        logger.info(f"Using output directory: {output_dir}")

        # Create evaluation result
        result = SemanticEvaluationResult(task_name, method_name, model_name)

        # Set generation time from metadata if available
        if hasattr(generation_result, 'metadata') and 'latency_seconds' in generation_result.metadata:
            result.generation_time = generation_result.metadata['latency_seconds']

        if not generation_result.success:
            result.invariant_generation_error = "Specification generation failed"
            result.overall_success = False
            return result

        # Determine working mode and prepare specification file
        if spec_file_path and Path(spec_file_path).exists():
            # Composite mode: Reuse existing spec file
            logger.info(f"✓ Composite mode: Reusing spec file from runtime check: {spec_file_path}")

            with open(spec_file_path, 'r', encoding='utf-8') as f:
                csp_content = f.read()

            # Create copy in invariant verification output directory
            spec_file = output_dir / f"{task_name}.csp"
            with open(spec_file, 'w', encoding='utf-8') as f:
                f.write(csp_content)
            result.specification_file = str(spec_file)
            logger.info(f"✓ Copied spec file to: {spec_file}")
        else:
            # Standalone mode: Create new spec file
            logger.info("✓ Standalone mode: Creating new spec file")
            spec_file = output_dir / f"{task_name}.csp"
            with open(spec_file, 'w', encoding='utf-8') as f:
                f.write(generation_result.generated_text)
            result.specification_file = str(spec_file)
            csp_content = generation_result.generated_text

        try:
            # Step 1: Load invariant templates
            logger.info("Step 1: Loading invariant templates...")
            templates = self.template_loader.load_task_invariants(task_name)
            logger.info(f"✓ Loaded {len(templates)} invariant templates")

            if not templates:
                result.invariant_generation_error = f"No invariant templates found for task: {task_name}"
                result.overall_success = False
                return result

            # Step 2: Translate invariants
            logger.info("Step 2: Translating invariants to CSP assertions...")
            translation_start = time.time()

            success, translations, error = self.translator.translate_all_invariants(
                templates, csp_content, task_name, model_name
            )

            result.invariant_generation_time = time.time() - translation_start

            if not success:
                result.invariant_generation_error = error
                result.overall_success = False
                return result

            logger.info(f"✓ Translated {len(translations)} invariants in {result.invariant_generation_time:.2f}s")

            # Save translated invariants
            translations_file = output_dir / f"{task_name}_translated_invariants.json"
            with open(translations_file, 'w', encoding='utf-8') as f:
                json.dump(translations, f, indent=2, ensure_ascii=False)
            logger.info(f"✓ Saved translations to: {translations_file}")

            # CRITICAL: Check if translations is empty
            # This can happen if LLM returns empty JSON or only comments
            if not translations or len(translations) == 0:
                error_msg = (
                    f"Translation produced no invariants (expected {len(templates)}, got 0). "
                    f"This may indicate LLM translation failure or empty response."
                )
                logger.error(error_msg)
                result.invariant_generation_error = error_msg
                result.model_checking_successful = False
                result.model_checking_error = "No invariants translated"
                result.total_invariants = 0
                result.invariants_passed = 0
                result.invariants_failed = 0
                result.overall_success = False
                return result

            # Step 3: Verify each invariant
            logger.info("Step 3: Verifying invariants with PAT...")
            invariant_results = self._verify_all_invariants(
                csp_content, translations, templates, task_name, output_dir
            )

            # Step 4: Aggregate results
            logger.info("Step 4: Aggregating results...")
            self._populate_evaluation_result(result, invariant_results)

            # Save detailed results
            self._save_detailed_results(output_dir, task_name, invariant_results, result)

            logger.info(
                f"✓ Invariant verification complete: "
                f"{result.invariants_passed}/{result.total_invariants} passed"
            )

        except FileNotFoundError as e:
            error_msg = f"Invariant templates not found: {e}"
            logger.error(error_msg)
            result.invariant_generation_error = error_msg
            result.overall_success = False

        except Exception as e:
            error_msg = f"Invariant evaluation failed: {e}"
            logger.error(error_msg, exc_info=True)
            result.invariant_generation_error = error_msg
            result.overall_success = False

        return result

    def _verify_all_invariants(
        self,
        original_csp: str,
        translations: Dict[str, str],
        templates: List[PATInvariantTemplate],
        task_name: str,
        output_dir: Path
    ) -> List[PATInvariantTestResult]:
        """
        Verify all translated invariants using PAT.

        Args:
            original_csp: Original CSP specification
            translations: Dictionary of {invariant_name: csp_assertion}
            templates: List of invariant templates
            task_name: Task name
            output_dir: Output directory

        Returns:
            List of PATInvariantTestResult
        """
        results = []
        template_dict = {t.name: t for t in templates}

        for inv_name, inv_assertion in translations.items():
            logger.info(f"Verifying invariant: {inv_name}")

            # Get template for this invariant
            template = template_dict.get(inv_name)
            if not template:
                logger.warning(f"No template found for: {inv_name}")
                continue

            # Compose specification with invariant
            augmented_csp = self._compose_spec_with_invariant(original_csp, inv_assertion)

            # Save augmented spec
            augmented_file = output_dir / f"{task_name}_{inv_name}.csp"
            augmented_file.write_text(augmented_csp, encoding='utf-8')

            # Run PAT
            verification_start = time.time()
            runtime_result = self.runtime_executor.run(augmented_file)
            verification_time = time.time() - verification_start

            # Extract result
            inv_result = self._extract_invariant_result(
                inv_name, inv_assertion, runtime_result, verification_time
            )
            results.append(inv_result)

            logger.info(
                f"  Result: {'✓ PASS' if inv_result.success else '✗ FAIL'} "
                f"({inv_result.visited_states} states, {inv_result.verification_time:.3f}s)"
            )

        return results

    def _compose_spec_with_invariant(self, original_csp: str, assertion: str) -> str:
        """
        Compose original CSP with invariant assertion using static composition.

        Strategy:
        - Remove existing #assert lines from original
        - Append new assertion at the end

        Args:
            original_csp: Original CSP specification
            assertion: CSP assertion to add

        Returns:
            Augmented CSP specification
        """
        # Remove existing assertions
        lines = []
        for line in original_csp.split('\n'):
            stripped = line.strip()
            # Skip #assert and #define lines that look like assertions
            if not (stripped.startswith('#assert') or
                    (stripped.startswith('#define') and ('|=' in stripped or 'deadlock' in stripped.lower()))):
                lines.append(line)

        # Add new assertion
        augmented = '\n'.join(lines).rstrip() + '\n\n' + assertion.strip() + '\n'

        return augmented

    def _extract_invariant_result(
        self,
        inv_name: str,
        inv_assertion: str,
        runtime_result: Dict,
        verification_time: float
    ) -> PATInvariantTestResult:
        """
        Extract invariant test result from PAT runtime result.

        Args:
            inv_name: Invariant name
            inv_assertion: CSP assertion
            runtime_result: Result from PATRuntimeExecutor
            verification_time: Verification time in seconds

        Returns:
            PATInvariantTestResult
        """
        if runtime_result['success']:
            # Check if all assertions passed
            passed = runtime_result.get('passed_assertions', 0)
            failed = runtime_result.get('failed_assertions', 0)

            success = (passed > 0 and failed == 0)

            # Extract states explored
            total_states = sum(
                a.get('visited_states', 0)
                for a in runtime_result.get('assertions', [])
            )

            # Get PAT output
            pat_output = ""
            for assertion in runtime_result.get('assertions', []):
                pat_output += f"Result: {assertion.get('result', 'UNKNOWN')}\n"
                pat_output += f"States: {assertion.get('visited_states', 0)}\n"

            return PATInvariantTestResult(
                name=inv_name,
                success=success,
                translated_invariant=inv_assertion,
                visited_states=total_states,
                verification_time=verification_time,
                pat_output=pat_output
            )
        else:
            # Verification failed
            error_msg = runtime_result.get('error', 'Unknown error')

            return PATInvariantTestResult(
                name=inv_name,
                success=False,
                translated_invariant=inv_assertion,
                error_message=error_msg,
                verification_time=verification_time,
                pat_output=error_msg
            )

    def _populate_evaluation_result(
        self,
        result: SemanticEvaluationResult,
        invariant_results: List[PATInvariantTestResult]
    ):
        """
        Populate evaluation result with invariant testing metrics.

        Args:
            result: SemanticEvaluationResult to populate
            invariant_results: List of invariant test results
        """
        result.total_invariants = len(invariant_results)
        result.invariants_passed = sum(1 for r in invariant_results if r.success)
        result.invariants_failed = result.total_invariants - result.invariants_passed

        # Total states explored across all invariants
        result.states_explored = sum(r.visited_states for r in invariant_results)

        # Total verification time
        result.model_checking_time = sum(r.verification_time for r in invariant_results)

        # CRITICAL: Set model_checking_successful and model_checking_error
        # This is required for SemanticEvaluationResult.to_dict() to report correctly
        if result.total_invariants == 0:
            # No invariants verified - this is a failure (empty translation or no templates)
            result.model_checking_successful = False
            result.model_checking_error = "No invariants were verified (empty translation or no templates)"
            result.overall_success = False
            logger.warning("No invariants verified - marking as failure")
        elif result.invariants_failed > 0:
            # Some invariants failed
            result.model_checking_successful = False
            failed_names = [r.name for r in invariant_results if not r.success]
            result.model_checking_error = (
                f"{result.invariants_failed} invariant(s) failed: {', '.join(failed_names[:3])}"
                + ("..." if len(failed_names) > 3 else "")
            )
            result.overall_success = False
        else:
            # All invariants passed
            result.model_checking_successful = True
            result.model_checking_error = None
            result.overall_success = True

        # Detailed output
        result.model_checking_output = self._format_invariant_output(invariant_results)

        logger.info(
            f"Invariant results: {result.invariants_passed}/{result.total_invariants} passed, "
            f"{result.states_explored} states, {result.model_checking_time:.2f}s"
        )

    def _format_invariant_output(self, invariant_results: List[PATInvariantTestResult]) -> str:
        """
        Format invariant results into human-readable output.

        Args:
            invariant_results: List of invariant test results

        Returns:
            Formatted string
        """
        lines = [
            "PAT Invariant Verification Results",
            "=" * 60,
            ""
        ]

        for i, inv_result in enumerate(invariant_results, 1):
            status = "✓ PASS" if inv_result.success else "✗ FAIL"
            lines.append(f"Invariant {i}: {inv_result.name} - {status}")
            lines.append(f"  States Explored: {inv_result.visited_states}")
            lines.append(f"  Verification Time: {inv_result.verification_time:.3f}s")

            if not inv_result.success and inv_result.error_message:
                lines.append(f"  Error: {inv_result.error_message[:200]}")

            lines.append("")

        return "\n".join(lines)

    def _save_detailed_results(
        self,
        output_dir: Path,
        task_name: str,
        invariant_results: List[PATInvariantTestResult],
        eval_result: SemanticEvaluationResult
    ):
        """
        Save detailed invariant results to JSON.

        Args:
            output_dir: Output directory
            task_name: Task name
            invariant_results: List of invariant results
            eval_result: Evaluation result
        """
        try:
            results_file = output_dir / f"{task_name}_invariant_results.json"

            detailed_results = {
                "task_name": task_name,
                "total_invariants": eval_result.total_invariants,
                "invariants_passed": eval_result.invariants_passed,
                "invariants_failed": eval_result.invariants_failed,
                "total_states": eval_result.states_explored,
                "total_time": eval_result.model_checking_time,
                "invariants": [
                    {
                        "name": r.name,
                        "success": r.success,
                        "translated_invariant": r.translated_invariant,
                        "visited_states": r.visited_states,
                        "verification_time": r.verification_time,
                        "error_message": r.error_message
                    }
                    for r in invariant_results
                ]
            }

            with open(results_file, 'w', encoding='utf-8') as f:
                json.dump(detailed_results, f, indent=2, ensure_ascii=False)

            logger.info(f"✓ Saved detailed results to: {results_file}")

        except Exception as e:
            logger.warning(f"Failed to save detailed results: {e}")

    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "pat_invariant"
