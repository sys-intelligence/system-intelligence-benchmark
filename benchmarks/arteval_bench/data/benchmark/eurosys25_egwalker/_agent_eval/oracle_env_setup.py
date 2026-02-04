"""Environment setup oracle for the Eurosys'25 EGWALKER bundle.

Validates:
  - Required tools and minimum versions where applicable.
  - Repository directory exists.
  - Ground-truth reference files exist.
"""

from __future__ import annotations

from pathlib import Path
from typing import Mapping, Sequence

from evaluator.utils import EntryConfig, logger
from evaluator.oracle_env_setup_primitives import (
  DependencyVersionRequirement,
  FilesystemPathRequirement,
  OracleEnvSetupBase,
  PathType,
  Requirement,
  VersionCompare,
)

_REPO_KEY = "egwalker"


def _required_path(paths: Mapping[str, Path], key: str, *, label: str) -> Path:
  """Returns a required path from a mapping with a clear error."""
  try:
    return paths[key]
  except KeyError as e:
    raise ValueError(f"Missing {label}[{key!r}] in EntryConfig") from e


class OracleEnvSetup(OracleEnvSetupBase):
  """Validates environment prerequisites for EGWALKER."""

  def __init__(self, *, config: EntryConfig, logger: logger) -> None:
    super().__init__(logger)
    self._config = config

  def requirements(self) -> Sequence[Requirement]:
    repo_root = _required_path(
      self._config.repository_paths, self._config.name, label="repository_paths")

    reqs: list[Requirement] = [
      # Tooling.
      DependencyVersionRequirement(
        name="rustc",
        command=("rustc", "--version"),
        required_version=(1, 78, 0),
        compare=VersionCompare.GEQ,
      ),
      DependencyVersionRequirement(
        name="cargo",
        command=("cargo", "--version"),
        required_version=(1, 0, 0),
        compare=VersionCompare.GEQ,
      ),
      DependencyVersionRequirement(
        name="node",
        command=("node", "--version"),
        required_version=(0, 0, 0),
        compare=VersionCompare.GEQ,
      ),
      DependencyVersionRequirement(
        name="make",
        command=("make", "--version"),
        required_version=(0, 0, 0),
        compare=VersionCompare.GEQ,
        optional=True,
      ),

      # Repo directory.
      FilesystemPathRequirement(
        name="repo_root_exists",
        path=repo_root,
        path_type=PathType.DIRECTORY,
      ),
    ]

    # Reference files (required).
    for key, ref_path in sorted(self._config.ground_truth_paths.items()):
      reqs.append(
        FilesystemPathRequirement(
          name=f"reference_{key}_exists",
          path=ref_path,
          path_type=PathType.FILE,
        )
      )

    return reqs