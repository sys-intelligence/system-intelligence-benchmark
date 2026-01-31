"""Artifact build oracle for the Eurosys'25 EGWALKER artifact.

Validates:
  - Required repository working directories exist.
  - Build commands execute successfully (captures stdout/stderr/return code).
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

    # Normalize for downstream requirements.
    if self.cwd_relative is not None and not isinstance(self.cwd_relative, Path):
      object.__setattr__(self, "cwd_relative", Path(self.cwd_relative))

    # Freeze command to avoid accidental mutation.
    object.__setattr__(self, "command", tuple(self.command))


class OracleArtifactBuild(OracleArtifactBuildBase):
  """The artifact build oracle for artifact-core.

  Defaults:
   * Runs build commands in the repo keyed by config.name.
   * EntryConfig.repository_paths must contain an entry for config.name.
  """

  _DEFAULT_TARGET_SPECS: tuple[tuple[str, tuple[str, ...], float], ...] = (
    (
      "artifact-core: make tools",
      (
        "make",
        "-j8",
        "tools/diamond-types/target/release/dt",
        "tools/crdt-converter/target/release/crdt-converter",
        "tools/diamond-types/target/release/paper-stats",
        "tools/paper-benchmarks/target/memusage/paper-benchmarks",
        "tools/paper-benchmarks/target/release/paper-benchmarks",
        "tools/ot-bench/target/memusage/ot-bench",
        "tools/ot-bench/target/release/ot-bench",
      ),
      60.0,
    ),
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
      targets = self._make_default_targets()
    self._targets = tuple(targets)

    names = [t.name for t in self._targets]
    if len(names) != len(set(names)):
      raise ValueError(f"Duplicate build target names: {names!r}")

  def _make_default_targets(self) -> tuple[BuildTarget, ...]:
    """Creates default targets (stored in the EntryConfig object)."""
    return tuple(
      BuildTarget(name = name, command = command, timeout_seconds = timeout_seconds)
      for (name, command, timeout_seconds) in self._DEFAULT_TARGET_SPECS
    )

  def requirements(self) -> Sequence[BuildRequirement]:
    """Returns an ordered list of build requirements to validate."""
    return tuple(
      BuildCommandRequirement(
        name = target.name,
        optional = target.optional,
        cwd = self._config.repository_paths[self._config.name],
        command = target.command,
        cwd_relative = target.cwd_relative,
        timeout_seconds = target.timeout_seconds,
        env_overrides = target.env_overrides,
      )
      for target in self._targets
    )