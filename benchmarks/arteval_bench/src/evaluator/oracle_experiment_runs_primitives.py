"""Experiment runs oracle primitives.

This module provides:
  1. List-level similarity metrics (Jaccard, dot product, cosine, Pearson,
     min-max).
  2. Elementwise comparison utilities (equality, similarity scoring, threshold
     checks).
  3. Requirement types that adapt these comparisons into utils.CheckResult objects.
  4. An orchestrator base class that runs checks, logs results, and returns a
     pass/fail outcome.

Derived oracles typically only override requirements() to declare a list of
numeric comparison requirements (similarity or elementwise checks) to evaluate, but
they can customize metrics, thresholds, or comparison behavior if needed.
"""

from __future__ import annotations

import abc
import dataclasses
import enum
import math
import typing

from collections.abc import Callable, Sequence

from evaluator import utils


# ---------------------------------------------------------------------------
# Basic types and constants
# ---------------------------------------------------------------------------


_CmpT = typing.TypeVar("_CmpT")

@dataclasses.dataclass(frozen=True, slots=True, kw_only=True)
class Compared(typing.Generic[_CmpT]):
  """A single observed-vs-reference comparison record.

  Attributes:
    observed: Value produced by the experiment run.
    reference: Expected/ground-truth value.
    result: Comparison result (e.g., bool or float score).
  """

  observed: float
  reference: float
  result: _CmpT


# ---------------------------------------------------------------------------
# Helper functions
# ---------------------------------------------------------------------------


def _is_nan(x: float) -> bool:
  return math.isnan(x)


def _require_equal_lengths(
    left: Sequence[float],
    right: Sequence[float],
    *,
    label: str,
) -> None:
  if len(left) != len(right):
    raise ValueError(
        f"{label}: length mismatch: left has {len(left)}, right has {len(right)}"
    )


def _require_all_finite(values: Sequence[float], *, label: str) -> None:
  for i, v in enumerate(values):
    if not math.isfinite(v):
      raise ValueError(f"{label}: non-finite value at index {i}: {v!r}")


def _jaccard_set_similarity(left: Sequence[float],
                            right: Sequence[float]) -> float:
  """Jaccard similarity treating inputs as sets (order/duplicates ignored)."""

  def _normalize(x: float) -> object:
    if _is_nan(x):
      return ("nan",)
    return x

  left_norm = [_normalize(x) for x in left]
  right_norm = [_normalize(x) for x in right]

  a = set(left_norm)
  b = set(right_norm)

  if len(a) != len(left_norm):
    raise ValueError("jaccard_set_similarity: left input contains duplicates (multiset not allowed)")
  if len(b) != len(right_norm):
    raise ValueError("jaccard_set_similarity: right input contains duplicates (multiset not allowed)")

  union = a | b
  if not union:
    return 1.0
  return len(a & b) / len(union)


def _dot_product(left: Sequence[float], right: Sequence[float]) -> float:
  """Dot product (unbounded). Requires equal lengths and finite inputs."""
  _require_equal_lengths(left, right, label="dot_product")
  _require_all_finite(left, label="dot_product.left")
  _require_all_finite(right, label="dot_product.right")
  return sum(a * b for a, b in zip(left, right, strict=True))


def _cosine_similarity(left: Sequence[float], right: Sequence[float]) -> float:
  """Cosine similarity in [-1, 1]. Requires equal lengths and finite inputs.

  Policy for zero vectors:
    - If both have zero norm, returns 1.0 (identical "no-signal").
    - If exactly one has zero norm, returns 0.0.
  """
  _require_equal_lengths(left, right, label="cosine_similarity")
  _require_all_finite(left, label="cosine_similarity.left")
  _require_all_finite(right, label="cosine_similarity.right")

  dot = 0.0
  norm_left = 0.0
  norm_right = 0.0
  for a, b in zip(left, right, strict=True):
    dot += a * b
    norm_left += a * a
    norm_right += b * b

  if norm_left == 0.0 and norm_right == 0.0:
    return 1.0
  if norm_left == 0.0 or norm_right == 0.0:
    return 0.0
  return dot / (math.sqrt(norm_left) * math.sqrt(norm_right))


def _pearson_similarity(left: Sequence[float], right: Sequence[float]) -> float:
  """Pearson correlation coefficient in [-1, 1].

  Requires:
    - equal lengths
    - at least 2 samples
    - finite inputs

  Policy for zero variance:
    - If both are constant and identical, returns 1.0.
    - If either has zero variance but they differ, returns 0.0.
  """
  _require_equal_lengths(left, right, label="pearson_similarity")
  if len(left) < 2:
    raise ValueError(
        f"pearson_similarity: need at least 2 samples, got {len(left)}")
  _require_all_finite(left, label="pearson_similarity.left")
  _require_all_finite(right, label="pearson_similarity.right")

  n = float(len(left))
  mean_left = sum(left) / n
  mean_right = sum(right) / n

  cov = 0.0
  var_left = 0.0
  var_right = 0.0
  for a, b in zip(left, right, strict=True):
    da = a - mean_left
    db = b - mean_right
    cov += da * db
    var_left += da * da
    var_right += db * db

  if var_left == 0.0 and var_right == 0.0:
    return 1.0 if list(left) == list(right) else 0.0
  if var_left == 0.0 or var_right == 0.0:
    return 0.0

  return cov / (math.sqrt(var_left) * math.sqrt(var_right))


def _min_max_similarity(left: Sequence[float], right: Sequence[float]) -> float:
  """Min-max similarity in [0, 1] for nonnegative vectors.

  minmax(x, y) = sum_i min(x_i, y_i) / sum_i max(x_i, y_i)

  Requires:
    - equal lengths
    - finite inputs
    - nonnegative inputs

  Policy for all-zeros:
    - If denominator is 0.0, returns 1.0 (identical "no-signal").
  """
  _require_equal_lengths(left, right, label="min_max_similarity")
  _require_all_finite(left, label="min_max_similarity.left")
  _require_all_finite(right, label="min_max_similarity.right")

  num = 0.0
  den = 0.0
  for i, (a, b) in enumerate(zip(left, right, strict=True)):
    if a < 0.0 or b < 0.0:
      raise ValueError(
          f"min_max_similarity: negative value at index {i}: left={a!r}, right={b!r}"
      )
    num += min(a, b)
    den += max(a, b)

  if den == 0.0:
    return 1.0
  return num / den


def _numbers_equal(a: float, b: float, *, nan_equal: bool) -> bool:
  if nan_equal and _is_nan(a) and _is_nan(b):
    return True
  return a == b


def _default_numeric_similarity(a: float, b: float, *,
                                abs_epsilon: float) -> float:
  """Similarity score where 1.0 means identical; decreases with relative error.

    score = 1 - |a-b| / max(|a|, |b|, abs_epsilon)

  Special cases:
    - NaN vs NaN => 1.0, NaN vs non-NaN => 0.0
    - +inf vs +inf or -inf vs -inf => 1.0, otherwise 0.0
  """
  if _is_nan(a) or _is_nan(b):
    return 1.0 if (_is_nan(a) and _is_nan(b)) else 0.0

  if math.isinf(a) or math.isinf(b):
    return 1.0 if a == b else 0.0

  denom = max(abs(a), abs(b), abs_epsilon)
  score = 1.0 - (abs(a - b) / denom)

  if score < 0.0:
    return 0.0
  if score > 1.0:
    return 1.0
  return score



def _elementwise_similarity_scores(
    observed: Sequence[float],
    reference: Sequence[float],
    *,
    similarity_fn: Callable[[float, float], float] | None,
    abs_epsilon: float,
) -> list[Compared[float]]:
  _require_equal_lengths(observed,
                         reference,
                         label="elementwise_similarity_scores")
  if abs_epsilon <= 0:
    raise ValueError(f"elementwise_similarity_scores: abs_epsilon must be > 0")

  if similarity_fn is None:

    def similarity_fn(a: float, b: float) -> float:
      return _default_numeric_similarity(a, b, abs_epsilon=abs_epsilon)

  out: list[Compared[float]] = []
  for a, b in zip(observed, reference, strict=True):
    out.append(Compared(observed=a, reference=b, result=similarity_fn(a, b)))
  return out


def _elementwise_equal(
    observed: Sequence[float],
    reference: Sequence[float],
    *,
    nan_equal: bool,
) -> list[Compared[bool]]:
  _require_equal_lengths(observed, reference, label="elementwise_equal")
  out: list[Compared[bool]] = []
  for a, b in zip(observed, reference, strict=True):
    out.append(
        Compared(observed=a,
                 reference=b,
                 result=_numbers_equal(a, b, nan_equal=nan_equal)))
  return out


def _summarize_mismatches_bool(
    comparisons: Sequence[Compared[bool]],
    *,
    max_items: int = 10,
) -> str:
  mismatches: list[str] = []
  total_bad = 0
  for i, c in enumerate(comparisons):
    if not c.result:
      total_bad += 1
      if len(mismatches) < max_items:
        mismatches.append(
            f"[{i}] observed={c.observed!r}, reference={c.reference!r}")
  if not mismatches:
    return ""
  more = total_bad - len(mismatches)
  suffix = f"\n... ({more} more)" if more > 0 else ""
  return "mismatches:\n" + "\n".join(mismatches) + suffix


def _summarize_mismatches_threshold(
    scores: Sequence[Compared[float]],
    *,
    threshold: float,
    max_items: int = 10,
) -> str:
  mismatches: list[str] = []
  total_bad = 0
  for i, c in enumerate(scores):
    if c.result < threshold:
      total_bad += 1
      if len(mismatches) < max_items:
        mismatches.append(
            f"[{i}] score={c.result:.6f} observed={c.observed!r}, reference={c.reference!r}"
        )
  if not mismatches:
    return ""
  more = total_bad - len(mismatches)
  suffix = f"\n... ({more} more)" if more > 0 else ""
  return "mismatches:\n" + "\n".join(mismatches) + suffix


# ---------------------------------------------------------------------------
# Oracle's core logic
# ---------------------------------------------------------------------------


@enum.unique
class SimilarityMetric(enum.Enum):
  """List-level metric identifier for computing a single similarity score."""

  JACCARD_SET = "jaccard_set"
  DOT_PRODUCT = "dot_product"
  COSINE = "cosine"
  PEARSON = "pearson"
  MIN_MAX = "min_max"


class SimilarityMetrics:
  """Namespace for list-level similarity metric implementations."""

  @staticmethod
  def compute(
      metric: SimilarityMetric,
      left: Sequence[float],
      right: Sequence[float],
  ) -> float:
    if metric == SimilarityMetric.JACCARD_SET:
      return _jaccard_set_similarity(left, right)
    if metric == SimilarityMetric.DOT_PRODUCT:
      return _dot_product(left, right)
    if metric == SimilarityMetric.COSINE:
      return _cosine_similarity(left, right)
    if metric == SimilarityMetric.PEARSON:
      return _pearson_similarity(left, right)
    if metric == SimilarityMetric.MIN_MAX:
      return _min_max_similarity(left, right)
    raise ValueError(f"unsupported similarity metric: {metric!r}")


class ElementwiseMetrics:
  """Namespace for elementwise comparison implementations."""

  @staticmethod
  def equal(
      observed: Sequence[float],
      reference: Sequence[float],
      *,
      nan_equal: bool = True,
  ) -> list[Compared[bool]]:
    return _elementwise_equal(observed, reference, nan_equal=nan_equal)

  @staticmethod
  def similarity_scores(
      observed: Sequence[float],
      reference: Sequence[float],
      *,
      similarity_fn: Callable[[float, float], float] | None = None,
      abs_epsilon: float = 1e-12,
  ) -> list[Compared[float]]:
    return _elementwise_similarity_scores(
        observed,
        reference,
        similarity_fn=similarity_fn,
        abs_epsilon=abs_epsilon,
    )

  @staticmethod
  def similarity_threshold(
      observed: Sequence[float],
      reference: Sequence[float],
      *,
      threshold: float,
      similarity_fn: Callable[[float, float], float] | None = None,
      abs_epsilon: float = 1e-12,
  ) -> list[Compared[bool]]:
    scores = ElementwiseMetrics.similarity_scores(
        observed,
        reference,
        similarity_fn=similarity_fn,
        abs_epsilon=abs_epsilon,
    )
    if not math.isfinite(threshold):
      raise ValueError(
          f"similarity_threshold: threshold must be finite, got {threshold!r}")

    out: list[Compared[bool]] = []
    for s in scores:
      out.append(
          Compared(observed=s.observed,
                   reference=s.reference,
                   result=(s.result >= threshold)))
    return out


@dataclasses.dataclass(...)
class ExperimentRunsContext:
  """Context passed to experiment-run requirements.

  Attributes:
    logger: Logger for diagnostics and shared policies.
  """

  logger: object


@dataclasses.dataclass(frozen=True, slots=True, kw_only=True)
class ListSimilarityRequirement(utils.BaseRequirement):
  """Checks a list-level similarity metric against a minimum score.

  Attributes:
    name: Human-readable requirement name for logs and reports.
    optional: Whether failure should be treated as a warning instead of an error.
    observed: Observed numeric sequence.
    reference: Reference numeric sequence.
    metric: Similarity metric to compute.
    min_similarity: Minimum acceptable similarity score.
  """

  observed: Sequence[float]
  reference: Sequence[float]
  metric: SimilarityMetric = SimilarityMetric.JACCARD_SET
  min_similarity: float = 1.0

  def __post_init__(self) -> None:
    if not math.isfinite(self.min_similarity):
      raise ValueError(f"{self.name}: min_similarity must be finite")
    object.__setattr__(self, "observed", tuple(self.observed))
    object.__setattr__(self, "reference", tuple(self.reference))

  def check(self, ctx: ExperimentRunsContext) -> utils.CheckResult:
    del ctx  # Reserved for shared policies/logging
    try:
      score = SimilarityMetrics.compute(self.metric, self.observed,
                                        self.reference)
    except ValueError as exc:
      return utils.CheckResult.failure(str(exc))

    if score < self.min_similarity:
      return utils.CheckResult.failure(
          f"{self.metric.value} similarity {score:.6f} < min_similarity {self.min_similarity:.6f}"
      )
    return utils.CheckResult.success()


@dataclasses.dataclass(frozen=True, slots=True, kw_only=True)
class ElementwiseEqualityRequirement(utils.BaseRequirement):
  """Checks elementwise equality for all entries.

  Attributes:
    name: Human-readable requirement name for logs and reports.
    optional: Whether failure should be treated as a warning instead of an error.
    observed: Observed numeric sequence.
    reference: Reference numeric sequence.
    nan_equal: Whether NaN should be considered equal to NaN.
    max_mismatches_to_report: Maximum mismatches to include in the failure message.
  """

  observed: Sequence[float]
  reference: Sequence[float]
  nan_equal: bool = True
  max_mismatches_to_report: int = 10

  def __post_init__(self) -> None:
    if self.max_mismatches_to_report <= 0:
      raise ValueError(f"{self.name}: max_mismatches_to_report must be > 0")
    object.__setattr__(self, "observed", tuple(self.observed))
    object.__setattr__(self, "reference", tuple(self.reference))

  def check(self, ctx: ExperimentRunsContext) -> utils.CheckResult:
    del ctx
    try:
      comps = ElementwiseMetrics.equal(self.observed,
                                       self.reference,
                                       nan_equal=self.nan_equal)
    except ValueError as exc:
      return utils.CheckResult.failure(str(exc))

    if all(c.result for c in comps):
      return utils.CheckResult.success()

    detail = _summarize_mismatches_bool(comps,
                                        max_items=self.max_mismatches_to_report)
    msg = "elementwise equality check failed"
    if detail:
      msg = f"{msg}\n{detail}"
    return utils.CheckResult.failure(msg)


@dataclasses.dataclass(frozen=True, slots=True, kw_only=True)
class ElementwiseSimilarityThresholdRequirement(utils.BaseRequirement):
  """Checks elementwise similarity scores against a threshold for all entries.

  Attributes:
    name: Human-readable requirement name for logs and reports.
    optional: Whether failure should be treated as a warning instead of an error.
    observed: Observed numeric sequence.
    reference: Reference numeric sequence.
    threshold: Minimum acceptable similarity score for each element.
    abs_epsilon: Absolute epsilon used by the default similarity function.
    max_mismatches_to_report: Maximum mismatches to include in the failure message.
  """

  observed: Sequence[float]
  reference: Sequence[float]
  threshold: float
  abs_epsilon: float = 1e-12
  max_mismatches_to_report: int = 10

  def __post_init__(self) -> None:
    if not math.isfinite(self.threshold):
      raise ValueError(f"{self.name}: threshold must be finite")
    if self.abs_epsilon <= 0:
      raise ValueError(f"{self.name}: abs_epsilon must be > 0")
    if self.max_mismatches_to_report <= 0:
      raise ValueError(f"{self.name}: max_mismatches_to_report must be > 0")
    object.__setattr__(self, "observed", tuple(self.observed))
    object.__setattr__(self, "reference", tuple(self.reference))

  def check(self, ctx: ExperimentRunsContext) -> utils.CheckResult:
    del ctx
    try:
      scores = ElementwiseMetrics.similarity_scores(
          self.observed,
          self.reference,
          abs_epsilon=self.abs_epsilon,
      )
    except ValueError as exc:
      return utils.CheckResult.failure(str(exc))

    if all(s.result >= self.threshold for s in scores):
      return utils.CheckResult.success()

    detail = _summarize_mismatches_threshold(
        scores,
        threshold=self.threshold,
        max_items=self.max_mismatches_to_report,
    )
    msg = f"elementwise similarity below threshold {self.threshold:.6f}"
    if detail:
      msg = f"{msg}\n{detail}"
    return utils.CheckResult.failure(msg)


class OracleExperimentRunsBase(abc.ABC):
  """Base class for an experiment-runs oracle.

  Derived classes typically implement requirements() to declare experiment checks.

  Attributes:
    _logger: Logger used for reporting and diagnostics.
  """

  _ORACLE_NAME = "ExperimentRuns"

  def __init__(self, *, logger: object) -> None:
    self._logger = logger

  @staticmethod
  def similarity(
      metric: SimilarityMetric,
      left: Sequence[float],
      right: Sequence[float],
  ) -> float:
    return SimilarityMetrics.compute(metric, left, right)

  @staticmethod
  def elementwise_equal(
      observed: Sequence[float],
      reference: Sequence[float],
      *,
      nan_equal: bool = True,
  ) -> list[Compared[bool]]:
    return ElementwiseMetrics.equal(observed, reference, nan_equal=nan_equal)

  @staticmethod
  def elementwise_similarity_scores(
      observed: Sequence[float],
      reference: Sequence[float],
      *,
      abs_epsilon: float = 1e-12,
  ) -> list[Compared[float]]:
    return ElementwiseMetrics.similarity_scores(observed,
                                                reference,
                                                abs_epsilon=abs_epsilon)

  @abc.abstractmethod
  def requirements(self) -> Sequence[utils.BaseRequirement]:
    """Returns an ordered list of requirements to validate."""
    raise NotImplementedError

  def report(self) -> utils.OracleReport:
    """Executes requirements and returns a structured report."""
    ctx = ExperimentRunsContext(logger=self._logger)
    return utils.build_oracle_report(
        logger=self._logger,
        requirements_fn=self.requirements,
        check_fn=lambda req: req.check(ctx),
    )

  def run(self, *, verbose: bool = False) -> bool:
    """Returns True iff all required checks pass (logs results)."""
    rep = self.report()
    return utils.log_oracle_report(self._logger,
                                   label=self._ORACLE_NAME,
                                   report=rep,
                                   verbose=verbose)
