#!/usr/bin/env python3
"""Benchmark preparation oracle for _agent_eval bundles.

Validates:
  - Dataset manifest JSON is readable and well-formed.
  - Each referenced dataset file is within the repo root (no traversal).
  - Each referenced dataset file exists and matches the expected size in bytes.
"""

from __future__ import annotations

import json
import logging
import sys
from pathlib import Path
from typing import Mapping, Sequence

from evaluator.utils import EntryConfig
from evaluator.oracle_benchmark_prep_primitives import (
    BenchmarkRequirement,
    FailRequirement,
    OracleBenchmarkPrepBase,
    Requirement,
)


def _required_path(paths: Mapping[str, Path], key: str, *, label: str) -> Path:
  """Returns a required path from a mapping with a clear error."""
  try:
    return paths[key]
  except KeyError as e:
    raise ValueError(f"Missing {label}[{key!r}] in EntryConfig") from e


def _resolve_nonstrict(path: Path) -> Path:
  """Resolves a path without requiring it to exist."""
  return path.resolve(strict = False)


def _is_within(root: Path, candidate: Path) -> bool:
  """Returns True iff candidate is within root after resolution."""
  root_resolved = _resolve_nonstrict(root)
  cand_resolved = _resolve_nonstrict(candidate)
  return cand_resolved == root_resolved or root_resolved in cand_resolved.parents


class OracleBenchmarkPrep(OracleBenchmarkPrepBase):
  """Validates dataset prerequisites for _agent_eval bundles."""

  def __init__(
      self,
      *,
      config: EntryConfig,
      logger: logging.Logger,
      manifest_key: str = "datasets",
  ) -> None:
    super().__init__(logger = logger)
    self._config = config
    self._manifest_key = manifest_key

  def requirements(self) -> Sequence[Requirement]:
    repo_root = _required_path(
      self._config.repository_paths,
      self._config.name,
      label = "repository_paths",
    )
    manifest_path = _required_path(
      self._config.ground_truth_paths,
      self._manifest_key,
      label = "ground_truth_paths",
    )

    reqs: list[Requirement] = [
      BenchmarkRequirement(
        name = "repo_root_exists",
        filepath = repo_root,
      ),
      BenchmarkRequirement(
        name = "dataset_manifest_exists",
        filepath = manifest_path,
      ),
    ]

    if not manifest_path.exists():
      return reqs

    try:
      obj = json.loads(manifest_path.read_text(encoding = "utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
      reqs.append(
        FailRequirement(
          name = "dataset_manifest_readable",
          message = f"manifest unreadable: {exc}",
        )
      )
      return reqs

    if not isinstance(obj, list):
      reqs.append(
        FailRequirement(
          name = "dataset_manifest_format",
          message = "manifest JSON must be a list of objects",
        )
      )
      return reqs

    # Print a stable marker so signature matching is robust
    # and portable across different platforms
    size_script = (
      "import os, sys\n"
      "p = sys.argv[1]\n"
      "print(f'OK size = {os.path.getsize(p)}')\n"
    )

    for i, entry in enumerate(obj):
      entry_name = f"entry[{i}]"

      if not isinstance(entry, dict):
        reqs.append(
          FailRequirement(
            name = entry_name,
            message = "entry must be an object",
          )
        )
        continue

      filepath = entry.get("filepath")
      size = entry.get("sizeinbytes")

      if not isinstance(filepath, str) or not filepath.strip():
        reqs.append(
          FailRequirement(
            name = entry_name,
            message = "missing/invalid filepath",
          )
        )
        continue
      if not isinstance(size, int) or size < 0:
        reqs.append(
          FailRequirement(
            name = entry_name,
            message = f"{filepath!r}: missing/invalid sizeinbytes",
          )
        )
        continue

      rel = Path(filepath)
      if rel.is_absolute():
        reqs.append(
          FailRequirement(
            name = f"dataset:{filepath}",
            message = "absolute paths not allowed",
          )
        )
        continue

      full_path = repo_root / rel
      if not _is_within(repo_root, full_path):
        reqs.append(
          FailRequirement(
            name = f"dataset:{filepath}",
            message = "path escapes repo root (.. traversal not allowed)",
          )
        )
        continue

      reqs.append(
        BenchmarkRequirement(
          name = f"dataset:{filepath}",
          filepath = full_path,
          cmd = (sys.executable, "-c", size_script, str(full_path)),
          signature = f"OK size = {size}",
          timeout_seconds = 30.0,
        )
      )

    return reqs
