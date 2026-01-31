"""Artifact build oracle.

This module defines a concrete artifact-build oracle that declares build commands
using the primitives in oracle_artifact_build_primitives.py.

The oracle is intentionally simple: it declares an ordered list of build command
requirements and relies on the base class to execute them, log results, and
produce a structured report for main.py.

An EntryConfig instance is expected to be provided by main.py and must include
repository_paths entries for any referenced repo_key values.
"""

from __future__ import annotations
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, field
from evaluator.oracle_artifact_build_primitives import (
  BuildCommandRequirement,
  BuildRequirement,
  OracleArtifactBuildBase,
)
from evaluator.utils import EntryConfig
from pathlib import Path
import logging


@dataclass(frozen = True, slots = True, kw_only = True)
class BuildTarget:
  """Declarative description of one build command to run.

  Attributes:
    name: Display name used in logs and reports.
    repo_key: Key into EntryConfig.repository_paths.
    command: argv-style command to execute.
    cwd_relative: Optional subdirectory within the repo to execute from.
    optional: If True, failures are reported as warnings instead of errors.
    timeout_seconds: Per-command timeout.
    env_overrides: Environment variables to override for the command.
  """

  name: str
  repo_key: str
  command: Sequence[str]
  cwd_relative: Path | None = None
  optional: bool = False
  timeout_seconds: float = 60.0
  env_overrides: Mapping[str, str] = field(default_factory = dict)

  def __post_init__(self) -> None:
    if not self.name:
      raise ValueError("BuildTarget.name must be non-empty")
    if not self.repo_key:
      raise ValueError(f"{self.name}: repo_key must be non-empty")
    if not self.command:
      raise ValueError(f"{self.name}: command must be non-empty")
    if self.timeout_seconds <= 0:
      raise ValueError(f"{self.name}: timeout_seconds must be > 0")

    if self.cwd_relative is not None and not isinstance(self.cwd_relative, Path):
      object.__setattr__(self, "cwd_relative", Path(self.cwd_relative))

    object.__setattr__(self, "command", tuple(self.command))


DEFAULT_BUILD_TARGETS: tuple[BuildTarget, ...] = (
  BuildTarget(
    name = "acto: make lib",
    repo_key = "acto",
    command = ("make", "lib"),
    timeout_seconds = 60.0,
  ),
)


class OracleArtifactBuild(OracleArtifactBuildBase):
  """The artifact build oracle."""

  _DEFAULT_TARGET_SPECS: tuple[tuple[str, tuple[str, ...], float], ...] = (
    ("acto: make lib", ("make", "lib"), 60.0),
  )

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
      targets = self._make_default_targets(config)

    self._targets = tuple(targets)
    names = [t.name for t in self._targets]
    if len(names) != len(set(names)):
      raise ValueError(f"Duplicate build target names: {names!r}")

  def _make_default_targets(self, config: EntryConfig) -> tuple[BuildTarget, ...]:
    """Creates the default BuildTarget list for this config."""
    repo_key = config.name
    return tuple(
      BuildTarget(
        name = name,
        repo_key = repo_key,
        command = command,
        timeout_seconds = timeout_seconds,
      )
      for (name, command, timeout_seconds) in self._DEFAULT_TARGET_SPECS
    )

  def requirements(self) -> Sequence[BuildRequirement]:
    """Returns an ordered list of build requirements to validate."""
    requirements: list[BuildRequirement] = []
    for target in self._targets:
      requirements.append(
        BuildCommandRequirement(
          name = target.name,
          optional = target.optional,
          cwd = self._config.repository_paths[self._config.name],
          command = target.command,
          cwd_relative = target.cwd_relative,
          timeout_seconds = target.timeout_seconds,
          env_overrides = target.env_overrides,
        )
      )
    return requirements
