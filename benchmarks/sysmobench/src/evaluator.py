"""Evaluator orchestration for SysMoBench tasks."""

from __future__ import annotations

from dataclasses import dataclass, field
import tempfile
from pathlib import Path
from typing import Dict, List, Optional

from tla_eval.evaluation.semantics.manual_invariant_evaluator import ManualInvariantEvaluator
from tla_eval.evaluation.syntax.compilation_check import CompilationCheckEvaluator
from tla_eval.evaluation.semantics.runtime_coverage_evaluator import RuntimeCoverageEvaluator
from tla_eval.evaluation.consistency.trace_validation import TraceValidationEvaluator


@dataclass
class EvaluationOutcome:
    """Container for compilation/runtime evaluation artifacts."""

    compilation: object
    runtime: Optional[object]
    invariant: Optional[object]
    trace: Optional[object]
    success: bool
    errors: List[str]
    phase_scores: Dict[str, float] = field(default_factory=dict)
    normalized_weights: Dict[str, float] = field(default_factory=dict)


class SysMoEvaluator:
    """Wraps SysMoBench evaluators to provide a unified interface."""

    TRACE_ENABLED_TASKS_DEFAULT = {"spin"}

    def __init__(
        self,
        compilation_timeout: int = 60,
        runtime_simulations: int = 100,
        runtime_depth: int = 100,
        runtime_timeout: int = 300,
        invariant_timeout: int = 300,
        phase_weights: Optional[Dict[str, float]] = None,
        trace_enabled_tasks: Optional[List[str]] = None,
    ) -> None:
        self.compilation_eval = CompilationCheckEvaluator(validation_timeout=compilation_timeout)
        self.runtime_eval = RuntimeCoverageEvaluator(
            num_simulations=runtime_simulations,
            simulation_depth=runtime_depth,
            tlc_timeout=runtime_timeout,
        )
        # Only initialize invariant evaluator when its weight is non-zero to avoid unnecessary overhead
        default_weights = {
            "syntax": 0.25,
            "runtime": 0.25,
            "trace": 0.25,
            "invariant": 0.25,
        }
        self.phase_weights = default_weights
        if phase_weights:
            self.phase_weights.update(phase_weights)
        self.trace_enabled_tasks = set(trace_enabled_tasks or self.TRACE_ENABLED_TASKS_DEFAULT)
        self.invariant_eval = None
        if self.phase_weights.get("invariant", 0) > 0:
            self.invariant_eval = ManualInvariantEvaluator(tlc_timeout=invariant_timeout)

    def evaluate(self, generation_result, task, method_name: str, model_name: str) -> EvaluationOutcome:
        """Run compilation + runtime evaluation for a generated spec."""
        errors: List[str] = []
        runtime_result = None
        invariant_result = None
        trace_result = None
        phase_scores = {k: 0.0 for k in ["syntax", "runtime", "trace", "invariant"]}
        trace_enabled = self._is_trace_enabled(task.task_name)
        normalized_weights = self._build_normalized_weights(trace_enabled)

        comp_result = self.compilation_eval.evaluate(
            generation_result,
            task.task_name,
            method_name,
            model_name,
            task.spec_module,
        )
        phase_scores["syntax"] = self._compute_syntax_score(comp_result)

        if comp_result.overall_success:
            # Runtime coverage (phase 2)
            runtime_result = self.runtime_eval.evaluate(
                generation_result,
                task.task_name,
                method_name,
                model_name,
                task.spec_module,
            )
            phase_scores["runtime"] = self._compute_runtime_score(runtime_result)
            if not runtime_result.overall_success:
                errors.append(f"Runtime: {getattr(runtime_result, 'error_message', 'failed')}")

            # Invariant verification (phase 4) – optional, controlled by weight
            if self.invariant_eval and phase_scores["syntax"] == 1.0 and phase_scores["runtime"] == 1.0:
                try:
                    invariant_result = self.invariant_eval.evaluate(
                        generation_result,
                        task.task_name,
                        method_name,
                        model_name,
                        task.spec_module,
                    )
                    phase_scores["invariant"] = self._compute_invariant_score(invariant_result)
                    if not invariant_result.overall_success:
                        errors.append(f"Invariant: {getattr(invariant_result, 'model_checking_error', 'failed')}")
                except Exception as exc:  # pylint: disable=broad-exception-caught
                    errors.append(f"Invariant: {exc}")
                    invariant_result = None
            # Trace validation placeholder – only run when enabled and earlier phases are perfect
            if (
                trace_enabled
                and normalized_weights.get("trace", 0) > 0
                and phase_scores["syntax"] == 1.0
                and phase_scores["runtime"] == 1.0
            ):
                trace_result = self._run_trace_validation(
                    generation_result,
                    task,
                    method_name,
                    model_name,
                )
                phase_scores["trace"] = self._compute_trace_score(trace_result)
                if not getattr(trace_result, "overall_success", False):
                    error_msg = getattr(trace_result, "trace_validation_error", None) or "Trace validation failed"
                    errors.append(f"Trace: {error_msg}")
        else:
            success = False
            errors.extend([f"Compilation: {err}" for err in comp_result.syntax_errors + comp_result.semantic_errors])

        # Overall success requires all executed phases to pass
        success = (
            comp_result.overall_success
            and (runtime_result.overall_success if runtime_result else True)
            and (invariant_result.overall_success if invariant_result else True)
        )

        return EvaluationOutcome(
            compilation=comp_result,
            runtime=runtime_result,
            invariant=invariant_result,
            trace=trace_result,
            success=success,
            errors=errors,
            phase_scores=phase_scores,
            normalized_weights=normalized_weights,
        )

    def compute_score(self, outcome: Optional[EvaluationOutcome]) -> float:
        """Compute weighted final score across phases."""
        if outcome is None:
            return 0.0

        total = 0.0
        weights = outcome.normalized_weights or self._build_normalized_weights(True)
        for phase, weight in weights.items():
            total += weight * outcome.phase_scores.get(phase, 0.0)
        return total

    @staticmethod
    def _compute_syntax_score(comp_result) -> float:
        """Compute syntax score with action-level granularity when available."""
        if comp_result is None:
            return 0.0
        if getattr(comp_result, "overall_success", False):
            return 1.0
        action_rate = comp_result.action_success_rate
        return max(0.0, min(1.0, action_rate))

    @staticmethod
    def _compute_runtime_score(runtime_result) -> float:
        """Compute runtime score using coverage metric when available."""
        if runtime_result is None or not getattr(runtime_result, "overall_success", False):
            return 0.0
        coverage = 0.0
        if hasattr(runtime_result, "custom_data"):
            coverage = runtime_result.custom_data.get("runtime_coverage_score", 0.0)
        return max(0.0, min(1.0, coverage))

    @staticmethod
    def _compute_invariant_score(invariant_result) -> float:
        """Compute invariant score based on pass ratio."""
        if invariant_result is None or not getattr(invariant_result, "custom_data", None):
            return 0.0
        custom = invariant_result.custom_data or {}
        passed = custom.get("passed_invariants", 0)
        total = custom.get("total_invariants", 0)
        if total > 0:
            return max(0.0, min(1.0, passed / total))
        return 1.0 if getattr(invariant_result, "overall_success", False) else 0.0

    @staticmethod
    def _compute_trace_score(trace_result) -> float:
        """Compute trace score as pass/fail."""
        if trace_result is None:
            return 0.0
        return 1.0 if getattr(trace_result, "overall_success", False) else 0.0

    def _is_trace_enabled(self, task_name: str) -> bool:
        """Return whether trace validation is enabled for the given task."""
        return task_name in self.trace_enabled_tasks

    def _build_normalized_weights(self, trace_enabled: bool) -> Dict[str, float]:
        """Return per-task normalized weights, dropping trace weight when disabled."""
        active_weights = dict(self.phase_weights)
        if not trace_enabled:
            active_weights.pop("trace", None)
        total_weight = sum(active_weights.values()) or 1.0
        return {k: v / total_weight for k, v in active_weights.items()}

    def _run_trace_validation(self, generation_result, task, method_name: str, model_name: str):
        """Execute trace validation metric using the generated spec."""
        try:
            with tempfile.TemporaryDirectory(prefix="sysmo_trace_") as tmpdir:
                tmpdir_path = Path(tmpdir)
                spec_path = tmpdir_path / f"{task.spec_module}.tla"
                spec_path.write_text(generation_result.generated_text, encoding="utf-8")

                cfg_path = tmpdir_path / f"{task.spec_module}.cfg"
                cfg_path.write_text(f"SPECIFICATION {task.spec_module}\n", encoding="utf-8")

                trace_eval = TraceValidationEvaluator(
                    spec_dir=str(tmpdir_path),
                    traces_dir="data/sys_traces",
                    with_exist_traces=20,  # Prefer existing traces to avoid regeneration when available
                )
                trace_result = trace_eval.evaluate(
                    task_name=task.task_name,
                    config={},
                    spec_file_path=str(spec_path),
                    config_file_path=str(cfg_path),
                )
                return trace_result
        except Exception as exc:  # pylint: disable=broad-exception-caught
            class TraceResult:
                overall_success = False
                trace_validation_error = str(exc)

            return TraceResult()
