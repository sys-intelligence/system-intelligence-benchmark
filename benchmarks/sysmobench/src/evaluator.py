"""Evaluator orchestration for SysMoBench tasks."""

from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional

from tla_eval.evaluation.syntax.compilation_check import CompilationCheckEvaluator
from tla_eval.evaluation.semantics.runtime_coverage_evaluator import RuntimeCoverageEvaluator


@dataclass
class EvaluationOutcome:
    """Container for compilation/runtime evaluation artifacts."""

    compilation: object
    runtime: Optional[object]
    success: bool
    errors: List[str]


class SysMoEvaluator:
    """Wraps SysMoBench evaluators to provide a unified interface."""

    def __init__(
        self,
        compilation_timeout: int = 60,
        runtime_simulations: int = 100,
        runtime_depth: int = 100,
        runtime_timeout: int = 300,
    ) -> None:
        self.compilation_eval = CompilationCheckEvaluator(validation_timeout=compilation_timeout)
        self.runtime_eval = RuntimeCoverageEvaluator(
            num_simulations=runtime_simulations,
            simulation_depth=runtime_depth,
            tlc_timeout=runtime_timeout,
        )

    def evaluate(self, generation_result, task, method_name: str, model_name: str) -> EvaluationOutcome:
        """Run compilation + runtime evaluation for a generated spec."""
        errors: List[str] = []
        runtime_result = None

        comp_result = self.compilation_eval.evaluate(
            generation_result,
            task.task_name,
            method_name,
            model_name,
            task.spec_module,
        )

        if comp_result.overall_success:
            runtime_result = self.runtime_eval.evaluate(
                generation_result,
                task.task_name,
                method_name,
                model_name,
                task.spec_module,
            )
            success = runtime_result.overall_success
            if not success:
                errors.append(f"Runtime: {getattr(runtime_result, 'error_message', 'failed')}")
        else:
            success = False
            errors.extend([f"Compilation: {err}" for err in comp_result.syntax_errors + comp_result.semantic_errors])

        return EvaluationOutcome(
            compilation=comp_result,
            runtime=runtime_result,
            success=success,
            errors=errors,
        )

    @staticmethod
    def final_score(outcome: Optional[EvaluationOutcome]) -> float:
        """Compute the final score from compilation/runtime outcomes."""
        if outcome is None:
            return 0.0

        comp_result = outcome.compilation
        runtime_result = outcome.runtime

        comp_score = 0.5 if getattr(comp_result, "overall_success", False) else 0.0
        runtime_score = 0.5 if (comp_score > 0 and runtime_result and getattr(runtime_result, "overall_success", False)) else 0.0

        return comp_score + runtime_score
