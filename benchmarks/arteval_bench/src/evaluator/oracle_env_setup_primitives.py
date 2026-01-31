"""Environment setup oracle primitives.

This module provides:
  1. Requirement types to specify environment dependencies, variables, and
     directory structure.
  2. An orchestrator base class that runs checks, logs results, and returns a
     pass/fail outcome.

Derived oracles typically only override requirements() to declare a list of
requirements to check, but they can customize behavior if needed.
"""

from __future__ import annotations

import abc
import dataclasses
import enum
import logging
import os
import re
import shutil
import subprocess

from collections.abc import Sequence
import pathlib

from evaluator import utils


# ------------------------------------------------------------------------------
# Basic types and constants
# ------------------------------------------------------------------------------


SemanticVersion = tuple[int, int, int]

@enum.unique
class VersionCompare(enum.Enum):
  """Comparison operator for validating a discovered version."""

  EQ = "eq"
  GEQ = "geq"
  LEQ = "leq"


@enum.unique
class EnvQuantifier(enum.Enum):
  """Matching mode for validating environment variable values."""

  EXACT = "exact"
  CONTAINS = "contains"
  REGEX = "regex"


@enum.unique
class PathType(enum.Enum):
  """Required filesystem object type for a path check."""

  ANY = "any"
  FILE = "file"
  DIRECTORY = "directory"


# ------------------------------------------------------------------------------
# Helper functions
# ------------------------------------------------------------------------------


def _parse_semantic_version(text: str) -> SemanticVersion | None:
  """Extract the first X.Y(.Z) token from text."""
  match = re.compile(r"(?:^|\s)v?(\d+)\.(\d+)(?:\.(\d+))?").search(text)
  if not match:
    return None
  major = int(match.group(1))
  minor = int(match.group(2))
  patch = int(match.group(3)) if match.group(3) is not None else 0
  return (major, minor, patch)


def _format_version(v: SemanticVersion) -> str:
  return f"{v[0]}.{v[1]}.{v[2]}"


def _normalize_path_entry(entry: str) -> str:
  """Normalizes a PATH entry for comparison across platforms."""
  return os.path.normcase(os.path.normpath(entry.strip()))


def _split_path_list(value: str) -> list[str]:
  return [e.strip() for e in value.split(os.pathsep) if e.strip()]


# ------------------------------------------------------------------------------
# Oracle's core logic
# ------------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True, slots=True, kw_only=True)
class DependencyVersionRequirement(utils.BaseRequirement):
  """Checks that an executable exists and satisfies a semantic version constraint.

  Attributes:
    name: Human-readable requirement name for logs and reports.
    optional: Whether failure should be treated as a warning instead of an error.
    command: Command argv used to query a version (e.g., ["python", "--version"]).
    required_version: Minimum/required semantic version as (major, minor, patch).
    compare: Comparison operator to apply against required_version.
    version_regex: Optional regex with a capturing group for the version token.
    timeout_seconds: Timeout for the version command, in seconds.
  """

  cmd: Sequence[str]
  required_version: SemanticVersion
  compare: VersionCompare = VersionCompare.GEQ
  version_regex: str | None = None
  timeout_seconds: float = 5.0

  _version_pattern: re.Pattern[str] | None = dataclasses.field(init=False,
                                                               repr=False,
                                                               default=None)

  def __post_init__(self) -> None:
    if not self.cmd:
      raise ValueError(f"{self.name}: command must be non-empty")
    if self.timeout_seconds <= 0:
      raise ValueError(f"{self.name}: timeout_seconds must be > 0")
    object.__setattr__(self, "command", tuple(self.cmd))

    if self.version_regex is not None:
      pattern = re.compile(self.version_regex, flags=re.IGNORECASE)
      if pattern.groups < 1:
        raise ValueError(
            f"{self.name}: version_regex must contain a capturing group")
      object.__setattr__(self, "_version_pattern", pattern)

  def check(self) -> utils.CheckResult:
    executable = self.cmd[0]
    resolved = shutil.which(executable)
    if resolved is None:
      return utils.CheckResult.failure(f"not found on PATH: {executable!r}")

    try:
      proc = subprocess.run(
          (resolved, *self.cmd[1:]),
          capture_output=True,
          text=True,
          check=False,
          timeout=self.timeout_seconds,
      )
      stdout = utils.decode_text(proc.stdout)
      stderr = utils.decode_text(proc.stderr)
    except subprocess.TimeoutExpired as exc:
      stdout = utils.decode_text(exc.stdout)
      stderr = utils.decode_text(exc.stderr)
      return utils.CheckResult.failure(
          f"version command timed out after {self.timeout_seconds}s",
          stdout=stdout,
          stderr=stderr,
          returncode=None,
          timed_out=True,
          cwd=None,
      )
    except OSError as exc:
      return utils.CheckResult.failure(
          f"failed to run {executable!r}: {exc}",
          stdout="",
          stderr=str(exc),
          returncode=None,
          timed_out=False,
          cwd=None,
      )

    combined = (stdout + "\n" + stderr).strip()

    if proc.returncode != 0:
      detail = combined if combined else f"rc = {proc.returncode}"
      return utils.CheckResult.failure(
          f"version command failed: {detail}",
          stdout=stdout,
          stderr=stderr,
          returncode=proc.returncode,
          timed_out=False,
          cwd=None,
      )

    candidate = combined
    if self._version_pattern is not None:
      re_match = self._version_pattern.search(candidate)
      if not re_match:
        return utils.CheckResult.failure(
            "version_regex did not match output",
            stdout=stdout,
            stderr=stderr,
            returncode=proc.returncode,
        )
      candidate = re_match.group(1)

    found = _parse_semantic_version(candidate)
    if found is None:
      return utils.CheckResult.failure(
          "could not parse version from output",
          stdout=stdout,
          stderr=stderr,
          returncode=proc.returncode,
      )

    if self.compare == VersionCompare.EQ:
      ok = found == self.required_version
      op = "=="
    elif self.compare == VersionCompare.GEQ:
      ok = found >= self.required_version
      op = ">="
    else:
      ok = found <= self.required_version
      op = "<="

    if not ok:
      return utils.CheckResult.failure(
          f"version {_format_version(found)} does not satisfy "
          f"{op} {_format_version(self.required_version)}",
          stdout=stdout,
          stderr=stderr,
          returncode=proc.returncode,
      )
    return utils.CheckResult.success(
        stdout=stdout,
        stderr=stderr,
        returncode=proc.returncode,
        cwd=None,
    )


@dataclasses.dataclass(frozen=True, slots=True, kw_only=True)
class EnvironmentVariableRequirement(utils.BaseRequirement):
  """Validates an environment variable using exact/contains/regex semantics.

  Attributes:
    name: Human-readable requirement name for logs and reports.
    optional: Whether failure should be treated as a warning instead of an error.
    env_var: Environment variable name to check.
    expected: Expected value or expected entry/pattern (depending on quantifier).
    quantifier: Matching mode to apply when comparing actual vs expected.
  """

  env_var: str
  expected: str
  quantifier: EnvQuantifier = EnvQuantifier.EXACT

  _expected_pattern: re.Pattern[str] | None = dataclasses.field(init=False,
                                                                repr=False,
                                                                default=None)

  def __post_init__(self) -> None:
    if not self.env_var:
      raise ValueError(f"{self.name}: env_var must be non-empty")
    if self.quantifier in (EnvQuantifier.CONTAINS, EnvQuantifier.REGEX):
      if not self.expected:
        raise ValueError(f"{self.name}: expected must be non-empty")
    if self.quantifier == EnvQuantifier.REGEX:
      object.__setattr__(self, "_expected_pattern", re.compile(self.expected))

  def check(self) -> utils.CheckResult:
    actual = os.environ.get(self.env_var)
    if actual is None:
      return utils.CheckResult.failure("not set")

    if self.quantifier == EnvQuantifier.EXACT:
      if actual == self.expected:
        return utils.CheckResult.success()
      return utils.CheckResult.failure(
          f"expected {self.expected!r}, got {actual!r}")

    entries = _split_path_list(actual)

    if self.quantifier == EnvQuantifier.CONTAINS:
      want = _normalize_path_entry(self.expected)
      normalized = [_normalize_path_entry(e) for e in entries]
      if want in normalized:
        return utils.CheckResult.success()
      return utils.CheckResult.failure(f"missing entry {self.expected!r}")

    # EnvQuantifier.REGEX
    assert self._expected_pattern is not None
    if any(self._expected_pattern.search(e) for e in entries):
      return utils.CheckResult.success()
    return utils.CheckResult.failure(
        f"no entry matches regex {self.expected!r}")


@dataclasses.dataclass(frozen=True, slots=True, kw_only=True)
class FilesystemPathRequirement(utils.BaseRequirement):
  """Checks whether a filesystem path exists and optionally enforces its type.

  Attributes:
    name: Human-readable requirement name for logs and reports.
    optional: Whether failure should be treated as a warning instead of an error.
    path: Path to validate.
    path_type: Required type (any/file/directory).
  """

  path: pathlib.Path | str | os.PathLike[str]
  path_type: PathType = PathType.ANY

  def __post_init__(self) -> None:
    object.__setattr__(self, "path", utils.to_path(self.path))
    if str(self.path).strip() == "":
      raise ValueError(f"{self.name}: path must be non-empty")

  def check(self) -> utils.CheckResult:
    if not self.path.exists():
      if self.path_type == PathType.FILE:
        return utils.CheckResult.failure(f"file missing: {self.path}")
      if self.path_type == PathType.DIRECTORY:
        return utils.CheckResult.failure(f"directory missing: {self.path}")
      return utils.CheckResult.failure(f"path missing: {self.path}")

    if self.path_type == PathType.ANY:
      return utils.CheckResult.success()

    if self.path_type == PathType.FILE:
      if self.path.is_file():
        return utils.CheckResult.success()
      return utils.CheckResult.failure(f"expected file: {self.path}")

    # PathType.DIRECTORY
    if self.path.is_dir():
      return utils.CheckResult.success()
    return utils.CheckResult.failure(f"expected directory: {self.path}")
  

class OracleEnvSetupBase(abc.ABC):
  """Base class for an environment setup oracle.

  Derived classes typically implement requirements() to declare what to check.

  Attributes:
    _logger: Logger used for reporting and diagnostics.
  """

  _ORACLE_NAME = "EnvironmentSetup"

  def __init__(self, logger: logging.Logger) -> None:
    self._logger = logger

  @abc.abstractmethod
  def requirements(self) -> Sequence[utils.BaseRequirement]:
    """Returns an ordered list of requirements to validate."""
    raise NotImplementedError

  def report(self) -> utils.OracleReport:
    """Executes requirements and returns a structured report."""
    return utils.build_oracle_report(
        logger=self._logger,
        requirements_fn=self.requirements,
        check_fn=lambda req: req.check(),
    )

  def run(self, *, verbose: bool = False) -> bool:
    """Returns True iff all required checks pass (logs results)."""
    rep = self.report()
    return utils.log_oracle_report(self._logger,
                                   label=self._ORACLE_NAME,
                                   report=rep,
                                   verbose=verbose)
