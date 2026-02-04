#!/usr/bin/env python3
"""Environment setup oracle for the ANVIL bundle.

This implementation uses evaluator.oracle_env_setup_primitives for consistent
reporting and verbose failure logging.
"""

from __future__ import annotations

import dataclasses
import logging
import shutil
from collections.abc import Sequence
from pathlib import Path

from evaluator.utils import CheckResult, EntryConfig
from evaluator.oracle_env_setup_primitives import (
    DependencyVersionRequirement,
    EnvironmentVariableRequirement,
    EnvQuantifier,
    FilesystemPathRequirement,
    OracleEnvSetupBase,
    PathType,
    Requirement,
    VersionCompare,
)


@dataclasses.dataclass(frozen = True, slots = True, kw_only = True)
class ExecutableOnPathRequirement(Requirement):
  """Checks that an executable is present on PATH (no version constraint)."""

  executable: str

  def __post_init__(self) -> None:
    if not self.executable:
      raise ValueError(f"{self.name}: executable must be non-empty")

  def check(self) -> CheckResult:
    if shutil.which(self.executable) is None:
      return CheckResult.failure(f"not found on PATH: {self.executable!r}")
    return CheckResult.success()


class OracleEnvSetup(OracleEnvSetupBase):
  """Validates environment prerequisites for the ANVIL bundle."""

  def __init__(self, *, config: EntryConfig, logger: logging.Logger) -> None:
    super().__init__(logger = logger)
    self._config = config

  def requirements(self) -> Sequence[Requirement]:
    home_dir = self._config.home_dir
    venv_dir = home_dir / ".venv"
    go_root = Path.home() / "go"
    go_bin = go_root / "bin"

    reqs: list[Requirement] = [
        # Check dependencies
        DependencyVersionRequirement(
          name = "docker",
          command = ("docker", "--version"),
          required_version = (24, 0, 0),
          compare = VersionCompare.GEQ,
        ),
        DependencyVersionRequirement(
          name = "go",
          command = ("go", "version"),
          required_version = (1, 22, 0),
          compare = VersionCompare.GEQ,
          version_regex = r"go(\d+\.\d+(?:\.\d+)?)",
        ),
        DependencyVersionRequirement(
            name = "python3",
            command = ("python3", "--version"),
            required_version = (3, 10, 0),
            compare = VersionCompare.GEQ,
            version_regex = r"Python\s+([0-9.]+)",
        ),
        DependencyVersionRequirement(
          name = "pip3",
          command = ("pip3", "--version"),
          required_version = (24, 0, 0),
          compare = VersionCompare.GEQ,
        ),
        DependencyVersionRequirement(
            name = "kind",
            command = ("kind", "version"),
            required_version = (0, 20, 0),
            compare = VersionCompare.GEQ,
            version_regex = r"v([0-9.]+)",
        ),
        DependencyVersionRequirement(
            name = "kubectl",
            command = ("kubectl", "version", "--client", "--short"),
            required_version = (1, 22, 9),
            compare = VersionCompare.GEQ,
            version_regex = r"Client Version:\s+v?([0-9.]+)",
        ),

        # Check directory structure
        FilesystemPathRequirement(
            name = "venv_exists",
            path = venv_dir,
            path_type = PathType.DIRECTORY,
        ),
        FilesystemPathRequirement(
            name = "go_root_exists",
            path = go_root,
            path_type = PathType.DIRECTORY,
        ),

        # Check PATH contents
        EnvironmentVariableRequirement(
            name = "PATH_contains_go_root",
            env_var = "PATH",
            expected = str(go_root),
            quantifier = EnvQuantifier.CONTAINS,
        ),
        EnvironmentVariableRequirement(
            name = "PATH_contains_go_bin",
            env_var = "PATH",
            expected = str(go_bin),
            quantifier = EnvQuantifier.CONTAINS,
        ),
    ]

    # Check that the repo root directory is present
    for key, repo_root in sorted(self._config.repository_paths.items()):
      reqs.append(
          FilesystemPathRequirement(
              name = f"repo_exists:{key}",
              path = repo_root,
              path_type = PathType.DIRECTORY,
          )
      )

    return reqs
