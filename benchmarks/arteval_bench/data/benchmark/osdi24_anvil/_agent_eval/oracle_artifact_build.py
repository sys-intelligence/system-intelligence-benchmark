#!/usr/bin/env python3
"""Artifact build oracle for the OSDI '24 ANVIL artifact.

Validates:
  - The ACTO dependency repository can build its required library target.
"""

from __future__ import annotations

from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
import logging
from pathlib import Path

from evaluator.oracle_artifact_build_primitives import (
    BuildCommandRequirement,
    BuildRequirement,
    OracleArtifactBuildBase,
)
from evaluator.utils import EntryConfig


@dataclass(frozen = True, slots = True, kw_only = True)
class BuildTarget:
  """Declarative description of one build command to run."""

  name: str
  cwd: Path
  command: Sequence[str]
  cwd_relative: Path | None = None
  optional: bool = False
  timeout_seconds: float = 60.0
  env_overrides: Mapping[str, str] = field(default_factory = dict)

  def __post_init__(self) -> None:
    if not self.name:
      raise ValueError("BuildTarget.name must be non-empty")
    if not self.command:
      raise ValueError(f"{self.name}: command must be non-empty")
    if self.timeout_seconds <= 0:
      raise ValueError(f"{self.name}: timeout_seconds must be > 0")

    object.__setattr__(self, "command", tuple(self.command))


class OracleArtifactBuild(OracleArtifactBuildBase):
  """Artifact build oracle for ANVIL."""

  def __init__(
      self,
      *,
      config: EntryConfig,
      logger: logging.Logger,
      targets: Sequence[BuildTarget] | None = None,
  ) -> None:
    super().__init__(logger = logger)
    self._config = config

    if targets is None:
      targets = self._default_targets()
    self._targets = tuple(targets)

    names = [t.name for t in self._targets]
    if len(names) != len(set(names)):
      raise ValueError(f"Duplicate build target names: {names!r}")

  def _default_targets(self) -> tuple[BuildTarget, ...]:
    acto_repo = self._config.repository_paths["osdi24-acto-dependency"]
    return (
        BuildTarget(
            name = "acto: make lib",
            cwd = acto_repo,
            command = ("make", "lib"),
            timeout_seconds = 60.0,
        ),
    )

  def requirements(self) -> Sequence[BuildRequirement]:
    return tuple(
        BuildCommandRequirement(
            name = t.name,
            optional = t.optional,
            cwd = t.cwd,
            command = t.command,
            cwd_relative = t.cwd_relative,
            timeout_seconds = t.timeout_seconds,
            env_overrides = t.env_overrides,
        )
        for t in self._targets
    )