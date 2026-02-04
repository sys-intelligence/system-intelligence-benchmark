#!/usr/bin/env python3
"""Environment setup oracle for the SOSP'23 ACTO artifact.

Validates:
  - Required dependencies and minimum versions where applicable.
  - Repository directory exists.
  - Ground-truth reference files exist (required).
  - Result files exist (optional; typically generated later).
"""

from __future__ import annotations
from collections.abc import Mapping, Sequence
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
from evaluator.utils import EntryConfig
from pathlib import Path
import logging


def _required_path(paths: Mapping[str, Path], key: str, *, label: str) -> Path:
  """Returns a required path from a mapping with a clear error message.

  Args:
    paths: Mapping containing paths.
    key: Required key.
    label: Label used in error messages.

  Returns:
    The path from the mapping.

  Raises:
    ValueError: If the key is missing.
  """
  try:
    return paths[key]
  except KeyError as exc:
    raise ValueError(f"Missing {label}[{key!r}] in EntryConfig") from exc


class OracleEnvSetup(OracleEnvSetupBase):
  """Validates environment prerequisites for the ACTO _agent_eval bundle."""

  def __init__(self, *, config: EntryConfig, logger: logging.Logger) -> None:
    super().__init__(logger)
    self._config = config

  def requirements(self) -> Sequence[Requirement]:
    """Returns an ordered list of requirements to validate."""
    repo_root = _required_path(
      self._config.repository_paths,
      self._config.name,
      label = "repository_paths",
    )

    if not self._config.ground_truth_paths:
      raise ValueError("EntryConfig.ground_truth_paths must be non-empty")

    home_dir = self._config.home_dir
    venv_dir = home_dir / ".venv"
    go_root = home_dir / "go"
    go_bin = go_root / "bin"

    reqs: list[Requirement] = [
        # Docker 23.0.0+
        DependencyVersionRequirement(
          name = "docker",
          command = ("docker", "--version"),
          required_version = (23, 0, 0),
          compare = VersionCompare.GEQ,
        ),
        # pip 23.0.1+
        DependencyVersionRequirement(
          name = "pip3",
          command = ("pip3", "--version"),
          required_version = (23, 0, 1),
          compare = VersionCompare.GEQ,
        ),
        # Python 3.8+
        DependencyVersionRequirement(
          name = "python3",
          command = ("python3", "--version"),
          required_version = (3, 8, 0),
          compare = VersionCompare.GEQ,
          version_regex = r"Python\s+([0-9.]+)",
        ),
        # Go 1.20+
        DependencyVersionRequirement(
          name = "go",
          command = ("go", "version"),
          required_version = (1, 20, 0),
          compare = VersionCompare.GEQ,
          version_regex = r"go(\d+\.\d+(?:\.\d+)?)",
        ),
        # kind 0.20.0+
        DependencyVersionRequirement(
          name = "kind",
          command = ("kind", "version"),
          required_version = (0, 20, 0),
          compare = VersionCompare.GEQ,
          version_regex = r"v([0-9.]+)",
        ),
        # kubectl 1.22.9+
        DependencyVersionRequirement(
          name = "kubectl",
          command = ("kubectl", "version", "--client", "--short"),
          required_version = (1, 22, 9),
          compare = VersionCompare.GEQ,
          version_regex = r"Client Version:\s+v?([0-9.]+)",
        ),
        # Directory checks
        FilesystemPathRequirement(
          name = "repo_root_exists",
          path = repo_root,
          path_type = PathType.DIRECTORY,
        ),
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
        FilesystemPathRequirement(
            name = "go_bin_exists",
            path = go_bin,
            path_type = PathType.DIRECTORY,
        ),
        # PATH checks for Go
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

    for key, path in sorted(self._config.ground_truth_paths.items()):
      reqs.append(
          FilesystemPathRequirement(
            name = f"ground_truth[{key}]",
            path = path,
            path_type = PathType.FILE,
          )
      )

    for key, path in sorted(self._config.results_paths.items()):
      reqs.append(
          FilesystemPathRequirement(
            name = f"results[{key}]",
            optional = True,
            path = path,
            path_type = PathType.FILE,
          )
      )

    return tuple(reqs)
