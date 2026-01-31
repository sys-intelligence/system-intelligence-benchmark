#!/usr/bin/env python3
"""Experiment runs oracle for the EuroSys'25 EGWALKER artifact.

This oracle compares experiment-produced timings against reference timings.
"""

from __future__ import annotations

import json
from collections.abc import Iterable, Mapping, Sequence
from functools import partial
from pathlib import Path
import logging

from evaluator.oracle_experiment_runs_primitives import (
  ExperimentRunsRequirement,
  LabeledSequenceSimilarityThresholdRequirement,
  OracleExperimentRunsBase,
)
from evaluator.utils import EntryConfig


def _required_path(paths: Mapping[str, Path], key: str, *, label: str) -> Path:
  """Returns a required path from a mapping with a clear error message."""
  try:
    return paths[key]
  except KeyError as exc:
    raise ValueError(f"Missing {label}[{key!r}] in EntryConfig") from exc


def _loads_json_from_lines(lines: Sequence[str], *, label: str) -> object:
  """Parses JSON content from already-read file lines."""
  text = "\n".join(lines).strip()
  if not text:
    raise ValueError(f"{label}: empty JSON content")
  try:
    return json.loads(text)
  except json.JSONDecodeError as exc:
    raise ValueError(f"{label}: invalid JSON: {exc}") from exc


def _load_json_file(path: Path, *, label: str) -> object:
  """Loads JSON from a file path."""
  try:
    text = path.read_text(encoding="utf-8")
  except OSError as exc:
    raise ValueError(f"{label}: failed to read {path}: {exc}") from exc
  try:
    return json.loads(text)
  except json.JSONDecodeError as exc:
    raise ValueError(f"{label}: invalid JSON: {exc}") from exc


def _as_float(v: object, *, label: str) -> float:
  """Converts numeric values to float; raises on non-numeric."""
  if isinstance(v, (int, float)):
    return float(v)
  raise ValueError(f"{label}: non-numeric value {v!r}")


def _iter_metric_tag_rows(obj: object, *, label: str) -> Iterable[tuple[str, Mapping[str, object]]]:
  """Yields (row_key, stats_dict) where row_key is '<metric>.<tag>'."""
  if not isinstance(obj, dict):
    raise ValueError(f"{label}: timings JSON must be an object at top-level")

  for metric_name, metric in obj.items():
    if not isinstance(metric, dict):
      raise ValueError(f"{label}: {metric_name!r} must map to an object")
    for tag, stats in metric.items():
      if not isinstance(stats, dict):
        raise ValueError(f"{label}: {metric_name}.{tag} must map to an object")
      row_key = f"{metric_name}.{tag}"
      yield row_key, stats


def _discover_reference_fields(reference_obj: object, *, label: str) -> tuple[str, ...]:
  """Returns unique stats fields in order of first appearance in the reference."""
  seen: set[str] = set()
  ordered: list[str] = []
  for _row_key, stats in _iter_metric_tag_rows(reference_obj, label=label):
    for field in stats.keys():
      if not isinstance(field, str):
        raise ValueError(f"{label}: non-string field name {field!r}")
      if field not in seen:
        seen.add(field)
        ordered.append(field)
  return tuple(ordered)


def _pairs_for_field_from_obj(
    obj: object,
    *,
    field: str,
    label: str,
) -> list[tuple[str, float]]:
  """Builds (row_key, value) pairs for a given stats field."""
  out: list[tuple[str, float]] = []
  for row_key, stats in _iter_metric_tag_rows(obj, label=label):
    if field not in stats:
      # Skip: the primitives will treat this as "missing label" if reference
      # expected it for this field (i.e., if reference includes row_key here).
      continue
    out.append((row_key, _as_float(stats[field], label=f"{label}: {row_key}.{field}")))
  return out


def _pairs_flatten_all_fields(obj: object, *, label: str) -> list[tuple[str, float]]:
  """Fallback: flattens all fields into '<metric>.<tag>.<field>' labels."""
  out: list[tuple[str, float]] = []
  for row_key, stats in _iter_metric_tag_rows(obj, label=label):
    for field, raw in stats.items():
      if not isinstance(field, str):
        raise ValueError(f"{label}: non-string field name {field!r}")
      full = f"{row_key}.{field}"
      out.append((full, _as_float(raw, label=f"{label}: {full}")))
  return out


def _parse_results_pairs_for_field(lines: Sequence[str], *, field: str) -> list[tuple[str, float]]:
  obj = _loads_json_from_lines(lines, label="timings results")
  return _pairs_for_field_from_obj(obj, field=field, label="timings results")


def _parse_reference_pairs_for_field(path: Path, *, field: str) -> list[tuple[str, float]]:
  obj = _load_json_file(path, label="timings reference")
  return _pairs_for_field_from_obj(obj, field=field, label="timings reference")


def _parse_results_pairs_flat(lines: Sequence[str]) -> list[tuple[str, float]]:
  obj = _loads_json_from_lines(lines, label="timings results")
  return _pairs_flatten_all_fields(obj, label="timings results")


def _parse_reference_pairs_flat(path: Path) -> list[tuple[str, float]]:
  obj = _load_json_file(path, label="timings reference")
  return _pairs_flatten_all_fields(obj, label="timings reference")


class OracleExperimentRuns(OracleExperimentRunsBase):
  """Validates experiment run timings for EGWALKER."""

  _NAME = "ExperimentRuns"

  def __init__(self, *, config: EntryConfig, logger: logging.Logger) -> None:
    super().__init__(logger=logger)
    self._config = config

  def requirements(self) -> Sequence[ExperimentRunsRequirement]:
    if not self._config.results_paths:
      raise ValueError("EntryConfig.results_paths must be non-empty")
    if not self._config.ground_truth_paths:
      raise ValueError("EntryConfig.ground_truth_paths must be non-empty")

    results_path = _required_path(
      self._config.results_paths, "timings", label="results_paths"
    )
    reference_path = _required_path(
      self._config.ground_truth_paths, "timings", label="ground_truth_paths"
    )

    threshold = self._config.similarity_ratio

    # Discover which "types" (fields) to check from the reference.
    # If discovery fails (missing/invalid JSON), fall back to a single requirement
    # that will report the real failure via the primitives.
    try:
      ref_obj = _load_json_file(reference_path, label="timings reference")
      fields = _discover_reference_fields(ref_obj, label="timings reference")
    except ValueError:
      fields = ()

    if not fields:
      # Fallback or "no fields": compare all qualified fields as one sequence.
      return (
        LabeledSequenceSimilarityThresholdRequirement(
          name="timings",
          label="Timings",
          results_path=results_path,
          reference_path=reference_path,
          threshold=threshold,
          parse_results_fn=_parse_results_pairs_flat,
          parse_reference_fn=_parse_reference_pairs_flat,
        ),
      )

    reqs: list[ExperimentRunsRequirement] = []
    for field in fields:
      reqs.append(
        LabeledSequenceSimilarityThresholdRequirement(
          name=f"timings_{field}",
          label=f"Timings {field}",
          results_path=results_path,
          reference_path=reference_path,
          threshold=threshold,
          parse_results_fn=partial(_parse_results_pairs_for_field, field=field),
          parse_reference_fn=partial(_parse_reference_pairs_for_field, field=field),
        )
      )
    return tuple(reqs)