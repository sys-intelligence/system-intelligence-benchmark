"""Executor module that handles iterative generation/correction."""

from __future__ import annotations

import logging
import time
from dataclasses import dataclass
from typing import Optional

from tla_eval.config import get_configured_model
from tla_eval.models.base import GenerationResult

from evaluator import EvaluationOutcome, SysMoEvaluator


logger = logging.getLogger(__name__)


@dataclass
class ExecutorResult:
    """Result of executing the SysMoBench generation loop."""

    success: bool
    iteration: int
    total_time: float
    evaluation: Optional[EvaluationOutcome]
    generation: Optional[GenerationResult]
    error: Optional[str] = None


class SysMoExecutor:
    """Encapsulates generation + correction workflow."""

    def __init__(self, method, model_name: str, evaluator: SysMoEvaluator, max_iterations: int = 3) -> None:
        self.method = method
        self.model_name = model_name
        self.evaluator = evaluator
        self.max_iterations = max_iterations

    def run(self, task) -> ExecutorResult:
        """Generate a specification, iteratively apply corrections, and evaluate."""
        logger.info("Evaluating %s with max %s iterations", task.task_name, self.max_iterations)

        start = time.time()
        gen_result = self.method.generate(task, self.model_name)
        if not gen_result.success:
            return ExecutorResult(
                success=False,
                iteration=0,
                total_time=time.time() - start,
                evaluation=None,
                generation=None,
                error=gen_result.error_message,
            )

        current_spec = gen_result.tla_specification
        current_gen = GenerationResult(current_spec, gen_result.metadata, time.time(), True)
        last_outcome: Optional[EvaluationOutcome] = None

        for iteration in range(1, self.max_iterations + 1):
            logger.info("=== Iteration %s/%s ===", iteration, self.max_iterations)

            eval_outcome = self.evaluator.evaluate(current_gen, task, self.method.name, self.model_name)
            last_outcome = eval_outcome

            if eval_outcome.success:
                logger.info("  ✓ Compilation + Runtime PASS - SUCCESS at iteration %s", iteration)
                return ExecutorResult(
                    success=True,
                    iteration=iteration,
                    total_time=time.time() - start,
                    evaluation=eval_outcome,
                    generation=current_gen,
                )

            if iteration < self.max_iterations and hasattr(self.method, "_generate_correction"):
                errors = eval_outcome.errors
                logger.info("  Generating correction... (%s errors)", len(errors))
                model_obj = get_configured_model(self.model_name)
                correction = self.method._generate_correction(task, current_spec, errors, model_obj)
                if correction.success:
                    current_spec = correction.tla_specification
                    current_gen = GenerationResult(current_spec, correction.metadata, time.time(), True)
                    logger.info("  ✓ Corrected for iteration %s", iteration + 1)
                    continue

            logger.info("  No further corrections or reached max iterations.")

        return ExecutorResult(
            success=False,
            iteration=self.max_iterations,
            total_time=time.time() - start,
            evaluation=last_outcome,
            generation=current_gen,
        )
