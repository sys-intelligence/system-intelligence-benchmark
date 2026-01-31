"""Experiment runs oracle for TABLE-5..TABLE-8 (elementwise sequence checks).

This oracle validates that the tables produced by running the full set of 
experiments match reference JSON values elementwise (aligned by label) 
within a configurable  similarity threshold.
"""

from __future__ import annotations

import abc
import dataclasses
import json
import math
from collections.abc import Callable, Sequence
from pathlib import Path

from utils import RESULTS_PATH_TABLES, REFERENCE_PATH_TABLES, SIMILARITY_RATIO, logger

# Update this import path to wherever you placed the base primitives module.
from evaluator.oracles.experiment_runs_oracle_primitives import (  # pylint: disable=g-import-not-at-top
  ElementwiseMetrics,
  ExperimentRunRequirement,
  ExperimentRunsContext,
  OracleExperimentRunsBase,
)


# ---------------------------------------------------------------------------
# Helper functions
# ---------------------------------------------------------------------------


_LabeledIntPairs = list[tuple[str, int]]


def _normalize_label(label: str) -> str:
  """Canonicalizes labels for alignment (keeps case; collapses whitespace)."""
  return " ".join(label.split()).strip()


def _is_separator_line(line: str) -> bool:
  """Returns True if this is a header separator line (Markdown spaces/dashes)."""
  stripped = line.strip()
  if not stripped:
    return False
  return all(ch in "- " for ch in stripped)


def _read_nonempty_lines(path: Path) -> list[str]:
  """Reads file and returns non-empty lines with trailing newlines stripped."""
  text = path.read_text(encoding = "utf-8")
  return [line.rstrip("\n") for line in text.splitlines() if line.strip()]


def _parse_int_token(text: str, *, label: str) -> int:
  """Parses an integer allowing commas."""
  try:
    return int(text.replace(",", ""))
  except ValueError as exc:
    raise ValueError(f"{label}: unparseable int: {text!r}") from exc


def _extract_table_body(lines: Sequence[str], *, label: str) -> tuple[str, list[str]]:
  """Splits raw lines into (header_line, data_lines) after separator."""
  if not lines:
    raise ValueError(f"{label}: table is empty")

  header_line = lines[0]
  saw_separator = False
  data_lines: list[str] = []

  for line in lines[1:]:
    if not saw_separator and _is_separator_line(line):
      saw_separator = True
      continue
    if saw_separator:
      data_lines.append(line)

  if not saw_separator:
    raise ValueError(f"{label}: missing header separator line")

  return header_line, data_lines


def _load_json_object(path: Path, *, label: str) -> dict:
  """Loads a JSON file expected to contain an object."""
  try:
    raw = json.loads(path.read_text(encoding = "utf-8"))
  except json.JSONDecodeError as exc:
    raise ValueError(f"{label}: invalid JSON: {exc}") from exc

  if not isinstance(raw, dict):
    raise ValueError(f"{label}: must contain a JSON object")
  return raw


def _get_first_str_field(
    obj: dict,
    *,
    keys: Sequence[str],
    label: str,
) -> str:
  """Returns the first present string field among keys."""
  for k in keys:
    if k in obj:
      v = obj[k]
      if isinstance(v, str) and v.strip():
        return v
      raise ValueError(f"{label}: field {k!r} must be a non-empty string")
  raise ValueError(f"{label}: missing any of fields {list(keys)!r}")


def _get_first_int_field(
    obj: dict,
    *,
    keys: Sequence[str],
    label: str,
) -> int:
  """Returns the first present int-ish field among keys."""
  for k in keys:
    if k in obj:
      v = obj[k]
      try:
        return int(v)
      except (TypeError, ValueError) as exc:
        raise ValueError(f"{label}: field {k!r} must be an integer") from exc
  raise ValueError(f"{label}: missing any of fields {list(keys)!r}")


def _pairs_to_unique_map(
    pairs: _LabeledIntPairs,
    *,
    label: str,
) -> tuple[dict[str, int], list[str]]:
  """Builds a label->value map and preserves the (normalized) order from pairs."""
  mapping: dict[str, int] = {}
  order: list[str] = []
  for raw_label, value in pairs:
    key = _normalize_label(raw_label)
    if key in mapping:
      raise ValueError(f"{label}: duplicate label: {raw_label!r}")
    mapping[key] = value
    order.append(key)
  return mapping, order


def _summarize_labels(items: Sequence[str], *, max_items: int = 10) -> str:
  shown = list(items[:max_items])
  suffix = f", ... ({len(items) - len(shown)} more)" if len(items) > len(shown) else ""
  return ", ".join(shown) + suffix


def _align_by_reference(
    observed: _LabeledIntPairs,
    reference: _LabeledIntPairs,
    *,
    label: str,
) -> tuple[list[str], list[float], list[float]]:
  """Aligns observed/reference by label using reference order."""
  obs_map, _ = _pairs_to_unique_map(observed, label = f"{label}: observed")
  ref_map, ref_order = _pairs_to_unique_map(reference, label = f"{label}: reference")

  obs_keys = set(obs_map.keys())
  ref_keys = set(ref_map.keys())

  missing = sorted(ref_keys - obs_keys)
  extra = sorted(obs_keys - ref_keys)

  if missing:
    raise ValueError(
      f"{label}: missing labels in observed: {_summarize_labels(missing)}"
    )
  if extra:
    raise ValueError(
      f"{label}: extra labels in observed: {_summarize_labels(extra)}"
    )

  observed_values: list[float] = []
  reference_values: list[float] = []
  for key in ref_order:
    observed_values.append(float(obs_map[key]))
    reference_values.append(float(ref_map[key]))

  return ref_order, observed_values, reference_values


def _collect_threshold_mismatches(
    labels: Sequence[str],
    observed_values: Sequence[float],
    reference_values: Sequence[float],
    *,
    threshold: float,
    max_items: int,
) -> tuple[int, list[str]]:
  """Returns (num_failed, mismatch_lines) with score diagnostics."""
  scores = ElementwiseMetrics.similarity_scores(observed_values, reference_values)
  failures = 0
  lines: list[str] = []
  for i, s in enumerate(scores):
    if s.cmp < threshold:
      failures += 1
      if len(lines) < max_items:
        lines.append(
          f"[{labels[i]}] score={s.cmp:.6f} observed={s.observed!r} reference={s.reference!r}"
        )
  return failures, lines


# ---------------------------------------------------------------------------
# Experiment results parsing (Markdown-style)
# ---------------------------------------------------------------------------

_TABLE5_FIELDS: tuple[str, ...] = (
  "undesired_state",
  "system_error",
  "operator_error",
  "recovery_failure",
)


def _parse_table5_results_pairs(lines: Sequence[str], *, field: str) -> _LabeledIntPairs:
  """Parses TABLE-5 results and returns (operator, value) for one field."""
  if field not in _TABLE5_FIELDS:
    raise ValueError(f"TABLE-5: unsupported field: {field!r}")

  expected_headers = [
    "Operator",
    "Undesired State",
    "System Error",
    "Operator Error",
    "Recovery Failure",
    "Total",
  ]
  header_line, data_lines = _extract_table_body(lines, label = "TABLE-5")
  if any(h not in header_line for h in expected_headers):
    raise ValueError(f"TABLE-5: unexpected headers: {header_line!r}")

  out: _LabeledIntPairs = []
  for line in data_lines:
    parts = line.split()
    if len(parts) != 6:
      raise ValueError(
        f"TABLE-5: row has {len(parts)} fields, expected 6: {line!r}"
      )

    operator = parts[0]
    if operator == "Total":
      # Ignore aggregate totals row.
      continue

    undesired = _parse_int_token(parts[1], label = "TABLE-5 undesired_state")
    system_err = _parse_int_token(parts[2], label = "TABLE-5 system_error")
    operator_err = _parse_int_token(parts[3], label = "TABLE-5 operator_error")
    recovery_fail = _parse_int_token(parts[4], label = "TABLE-5 recovery_failure")
    # parts[5] is the per-operator "Total" column; ignore by design.

    if field == "undesired_state":
      out.append((operator, undesired))
    elif field == "system_error":
      out.append((operator, system_err))
    elif field == "operator_error":
      out.append((operator, operator_err))
    else:
      out.append((operator, recovery_fail))

  return out


def _parse_table6_results_pairs(lines: Sequence[str]) -> _LabeledIntPairs:
  """Parses TABLE-6 results and returns (label, bugs) pairs."""
  expected_headers = ["Consequence", "# Bugs"]
  header_line, data_lines = _extract_table_body(lines, label = "TABLE-6")
  if any(h not in header_line for h in expected_headers):
    raise ValueError(f"TABLE-6: unexpected headers: {header_line!r}")

  out: _LabeledIntPairs = []
  for line in data_lines:
    parts = line.split()
    if len(parts) < 2:
      raise ValueError(
        f"TABLE-6: row has {len(parts)} fields, expected at least 2: {line!r}"
      )
    label = " ".join(parts[:-1])
    bugs = _parse_int_token(parts[-1], label = "TABLE-6 bugs")
    out.append((label, bugs))
  return out


def _parse_table7_results_pairs(lines: Sequence[str]) -> _LabeledIntPairs:
  """Parses TABLE-7 results and returns (label, bugs) pairs (ignores % token)."""
  expected_headers = ["Test Oracle", "# Bugs (Percentage)"]
  header_line, data_lines = _extract_table_body(lines, label = "TABLE-7")
  if any(h not in header_line for h in expected_headers):
    raise ValueError(f"TABLE-7: unexpected headers: {header_line!r}")

  out: _LabeledIntPairs = []
  for line in data_lines:
    parts = line.split()
    if len(parts) < 2:
      raise ValueError(
        f"TABLE-7: row has {len(parts)} fields, expected at least 2: {line!r}"
      )

    last = parts[-1]
    if last.startswith("(") and last.endswith("%)"):
      if len(parts) < 3:
        raise ValueError(
          f"TABLE-7: malformed row with percentage but no integer: {line!r}"
        )
      bugs_str = parts[-2]
      label = " ".join(parts[:-2])
    else:
      bugs_str = parts[-1]
      label = " ".join(parts[:-1])

    bugs = _parse_int_token(bugs_str, label = "TABLE-7 bugs")
    out.append((label, bugs))

  return out


def _parse_table8_results_pairs(lines: Sequence[str]) -> _LabeledIntPairs:
  """Parses TABLE-8 results and returns (operator, operations) pairs."""
  expected_headers = ["Operator", "# Operations"]
  header_line, data_lines = _extract_table_body(lines, label = "TABLE-8")
  if any(h not in header_line for h in expected_headers):
    raise ValueError(f"TABLE-8: unexpected headers: {header_line!r}")

  out: _LabeledIntPairs = []
  for line in data_lines:
    parts = line.split()
    if len(parts) != 2:
      raise ValueError(
        f"TABLE-8: row has {len(parts)} fields, expected 2: {line!r}"
      )
    operator = parts[0]
    ops = _parse_int_token(parts[1], label = "TABLE-8 operations")
    out.append((operator, ops))

  return out


# ---------------------------------------------------------------------------
# Reference results parsing (JSON)
# ---------------------------------------------------------------------------

def _parse_table5_reference_pairs(path: Path, *, field: str) -> _LabeledIntPairs:
  """Parses TABLE-5 reference JSON and returns (operator, value) for one field."""
  if field not in _TABLE5_FIELDS:
    raise ValueError(f"TABLE-5 reference: unsupported field: {field!r}")

  raw = _load_json_object(path, label = "TABLE-5 reference")
  ops = raw.get("operators")
  if not isinstance(ops, list):
    raise ValueError("TABLE-5 reference: missing 'operators' list")

  out: _LabeledIntPairs = []
  for idx, obj in enumerate(ops):
    if not isinstance(obj, dict):
      raise ValueError(f"TABLE-5 reference: entry #{idx} is not an object")

    operator = _get_first_str_field(
      obj,
      keys = ("operator", "label"),
      label = f"TABLE-5 reference: entry #{idx}",
    )
    value = _get_first_int_field(
      obj,
      keys = (field, "value"),
      label = f"TABLE-5 reference: entry #{idx}",
    )
    # Ignore obj["total"] by design.
    out.append((operator, value))

  return out


def _parse_table6_reference_pairs(path: Path) -> _LabeledIntPairs:
  raw = _load_json_object(path, label = "TABLE-6 reference")
  items = raw.get("symptoms")
  if not isinstance(items, list):
    raise ValueError("TABLE-6 reference: missing 'symptoms' list")

  out: _LabeledIntPairs = []
  for idx, obj in enumerate(items):
    if not isinstance(obj, dict):
      raise ValueError(f"TABLE-6 reference: entry #{idx} is not an object")

    label = _get_first_str_field(
      obj,
      keys = ("symptom", "consequence", "label"),
      label = f"TABLE-6 reference: entry #{idx}",
    )
    value = _get_first_int_field(
      obj,
      keys = ("bugs", "value"),
      label = f"TABLE-6 reference: entry #{idx}",
    )
    out.append((label, value))

  return out


def _parse_table7_reference_pairs(path: Path) -> _LabeledIntPairs:
  raw = _load_json_object(path, label = "TABLE-7 reference")
  items = raw.get("test_oracles")
  if not isinstance(items, list):
    raise ValueError("TABLE-7 reference: missing 'test_oracles' list")

  out: _LabeledIntPairs = []
  for idx, obj in enumerate(items):
    if not isinstance(obj, dict):
      raise ValueError(f"TABLE-7 reference: entry #{idx} is not an object")

    label = _get_first_str_field(
      obj,
      keys = ("test_oracle", "oracle", "label"),
      label = f"TABLE-7 reference: entry #{idx}",
    )
    value = _get_first_int_field(
      obj,
      keys = ("bugs", "value"),
      label = f"TABLE-7 reference: entry #{idx}",
    )
    out.append((label, value))

  return out


def _parse_table8_reference_pairs(path: Path) -> _LabeledIntPairs:
  raw = _load_json_object(path, label = "TABLE-8 reference")
  items = raw.get("operators")
  if not isinstance(items, list):
    raise ValueError("TABLE-8 reference: missing 'operators' list")

  out: _LabeledIntPairs = []
  for idx, obj in enumerate(items):
    if not isinstance(obj, dict):
      raise ValueError(f"TABLE-8 reference: entry #{idx} is not an object")

    label = _get_first_str_field(
      obj,
      keys = ("operator", "label"),
      label = f"TABLE-8 reference: entry #{idx}",
    )
    value = _get_first_int_field(
      obj,
      keys = ("operations", "value"),
      label = f"TABLE-8 reference: entry #{idx}",
    )
    out.append((label, value))

  return out


# ---------------------------------------------------------------------------
# Similarity metadata
# ---------------------------------------------------------------------------

@dataclasses.dataclass(frozen = True, slots = True, kw_only = True)
class SimilarityRequirement(ExperimentRunRequirement):
  """Compares two labeled sequences elementwise under a similarity threshold."""

  label: str
  results_path: Path
  reference_path: Path
  threshold: float
  parse_results_fn: Callable[[Sequence[str]], _LabeledIntPairs]
  parse_reference_fn: Callable[[Path], _LabeledIntPairs]
  max_mismatches_to_report: int = 10

  def __post_init__(self) -> None:
    if not math.isfinite(self.threshold):
      raise ValueError(f"{self.name}: threshold must be finite")
    if self.threshold < 0.0 or self.threshold > 1.0:
      raise ValueError(f"{self.name}: threshold must be in [0, 1]")
    if self.max_mismatches_to_report <= 0:
      raise ValueError(f"{self.name}: max_mismatches_to_report must be > 0")
    object.__setattr__(self, "results_path", Path(self.results_path))
    object.__setattr__(self, "reference_path", Path(self.reference_path))

  def check(self, ctx: ExperimentRunsContext) -> "CheckResult":
    del ctx  # Reserved for shared policies/logging.

    # Match legacy behavior: check reference existence first.
    if not self.reference_path.exists():
      return CheckResult.failure(
        f"{self.reference_path} ({self.label} reference) not found"
      )
    if not self.results_path.exists():
      return CheckResult.failure(
        f"{self.results_path} ({self.label} results) not found"
      )

    try:
      lines = _read_nonempty_lines(self.results_path)
    except OSError as exc:
      return CheckResult.failure(f"{self.label}: failed to read results: {exc}")
    if not lines:
      return CheckResult.failure(f"{self.label}: results file is empty")

    try:
      observed_pairs = self.parse_results_fn(lines)
      reference_pairs = self.parse_reference_fn(self.reference_path)
    except ValueError as exc:
      return CheckResult.failure(str(exc))

    try:
      aligned_labels, observed_values, reference_values = _align_by_reference(
        observed_pairs,
        reference_pairs,
        label = self.label,
      )
    except ValueError as exc:
      return CheckResult.failure(str(exc))

    failures, mismatch_lines = _collect_threshold_mismatches(
      aligned_labels,
      observed_values,
      reference_values,
      threshold = self.threshold,
      max_items = self.max_mismatches_to_report,
    )

    if failures == 0:
      return CheckResult.success()

    msg = (
      f"{self.label}: {failures} entries below threshold {self.threshold:.6f}\n"
      "mismatches:\n" + "\n".join(mismatch_lines)
    )
    if failures > len(mismatch_lines):
      msg = f"{msg}\n... ({failures - len(mismatch_lines)} more)"
    return CheckResult.failure(msg)


# ---------------------------------------------------------------------------
# Oracle's main logic
# ---------------------------------------------------------------------------

class OracleExperimentRuns(OracleExperimentRunsBase):
  """Derived oracle that validates TABLE-5..TABLE-8 outputs."""

  _NAME = "ExperimentRuns"

  def __init__(self, *, threshold: float = SIMILARITY_RATIO) -> None:
    super().__init__(logger = logger)
    self._threshold = threshold

    self._table5_results_path = Path(RESULTS_PATH_TABLES["table5"])
    self._table5_reference_path = Path(REFERENCE_PATH_TABLES["table5"])
    self._table6_results_path = Path(RESULTS_PATH_TABLES["table6"])
    self._table6_reference_path = Path(REFERENCE_PATH_TABLES["table6"])
    self._table7_results_path = Path(RESULTS_PATH_TABLES["table7"])
    self._table7_reference_path = Path(REFERENCE_PATH_TABLES["table7"])
    self._table8_results_path = Path(RESULTS_PATH_TABLES["table8"])
    self._table8_reference_path = Path(REFERENCE_PATH_TABLES["table8"])

  def requirements(self) -> Sequence[ExperimentRunRequirement]:
    reqs: list[ExperimentRunRequirement] = []

    # TABLE-5 is parsed as 4 independent labeled sequences (by operator)
    for field in _TABLE5_FIELDS:
      def _make_results_fn(f: str) -> Callable[[Sequence[str]], _LabeledIntPairs]:
        return lambda lines: _parse_table5_results_pairs(lines, field = f)

      def _make_reference_fn(f: str) -> Callable[[Path], _LabeledIntPairs]:
        return lambda path: _parse_table5_reference_pairs(path, field = f)

      reqs.append(
        SimilarityRequirement(
          name = f"TABLE-5/{field}",
          label = f"TABLE-5 {field}",
          results_path = self._table5_results_path,
          reference_path = self._table5_reference_path,
          threshold = self._threshold,
          parse_results_fn = _make_results_fn(field),
          parse_reference_fn = _make_reference_fn(field),
        )
      )

    # Tabels 6, 7, and 8 (with 8 being optional)
    reqs.extend(
      [
        SimilarityRequirement(
          name = "TABLE-6",
          label = "TABLE-6",
          results_path = self._table6_results_path,
          reference_path = self._table6_reference_path,
          threshold = self._threshold,
          parse_results_fn = _parse_table6_results_pairs,
          parse_reference_fn = _parse_table6_reference_pairs,
        ),
        SimilarityRequirement(
          name = "TABLE-7",
          label = "TABLE-7",
          results_path = self._table7_results_path,
          reference_path = self._table7_reference_path,
          threshold = self._threshold,
          parse_results_fn = _parse_table7_results_pairs,
          parse_reference_fn = _parse_table7_reference_pairs,
        ),
        SimilarityRequirement(
          name = "TABLE-8",
          label = "TABLE-8",
          results_path = self._table8_results_path,
          reference_path = self._table8_reference_path,
          threshold = self._threshold,
          parse_results_fn = _parse_table8_results_pairs,
          parse_reference_fn = _parse_table8_reference_pairs,
        ),
      ]
    )

    return reqs
