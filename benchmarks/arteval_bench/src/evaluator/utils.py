"""Shared types and helpers for oracle evaluation.

Includes dataclasses for check outcomes and oracle reports, logger configuration,
and helper functions for building and logging oracle results.
"""

from __future__ import annotations

import dataclasses
import logging
import os
import pathlib
import typing
import sys

from collections.abc import Callable, MutableMapping, Sequence

# ------------------------------------------------------------------------------
# Constants and definitions
# ------------------------------------------------------------------------------

_LOG_FORMAT = "%(asctime)s | %(levelname)s | %(name)s | %(message)s"
_DATE_FORMAT = "%Y-%m-%d %H:%M:%S"

DEFAULT_MAX_TRUNCATED_MESSAGE_CHARS = 4096
DEFAULT_MAX_CAPTURE_CHARS = 32768

Version = typing.Tuple[int, int, int]


# ------------------------------------------------------------------------------
# Shared config helpers
# ----------------------------


@dataclasses.dataclass(frozen=True)
class EntryConfig:
  """Shared configuration contract across all evaluation bundles.

  Attributes:
    name: Entry name used for reporting.
    home_dir: Base directory for the entry.
    repository_paths: Named repository root paths.
    results_paths: Named result output paths.
    ground_truth_paths: Named ground-truth paths.
    similarity_ratio: Default similarity ratio threshold used by evaluators.
  """

  name: str
  home_dir: pathlib.Path

  repository_paths: typing.Dict[str, pathlib.Path] = typing.field(
      default_factory=dict)
  results_paths: typing.Dict[str,
                             pathlib.Path] = typing.field(default_factory=dict)
  ground_truth_paths: typing.Dict[str, pathlib.Path] = typing.field(
      default_factory=dict)

  similarity_ratio: float = 0.75


@dataclasses.dataclass(frozen=True, slots=True)
class CheckResult:
  """Result of running a single check.

  Attributes:
    ok: Whether the check passed.
    message: Short human-readable summary (suitable for logs/UI).
    stdout: Captured stdout, if applicable.
    stderr: Captured stderr, if applicable.
    returncode: Process return code, if applicable.
    timed_out: True if a subprocess timed out.
    cwd: Working directory used, if applicable.
  """

  ok: bool
  message: str = ""
  stdout: str = ""
  stderr: str = ""
  returncode: int | None = None
  timed_out: bool = False
  cwd: pathlib.Path | None = None

  @classmethod
  def success(
      cls,
      *,
      stdout: str = "",
      stderr: str = "",
      returncode: int | None = 0,
      cwd: pathlib.Path | None = None,
  ) -> "CheckResult":
    return cls(
        ok=True,
        message="",
        stdout=stdout,
        stderr=stderr,
        returncode=returncode,
        timed_out=False,
        cwd=cwd,
    )

  @classmethod
  def failure(
      cls,
      message: str,
      *,
      stdout: str = "",
      stderr: str = "",
      returncode: int | None = None,
      timed_out: bool = False,
      cwd: pathlib.Path | None = None,
  ) -> "CheckResult":
    return cls(
        ok=False,
        message=message,
        stdout=stdout,
        stderr=stderr,
        returncode=returncode,
        timed_out=timed_out,
        cwd=cwd,
    )


@dataclasses.dataclass(frozen=True, slots=True)
class RequirementOutcome:
  """Outcome of running one requirement.

  Attributes:
    name: Requirement name.
    optional: Whether this requirement is optional.
    result: Result of running the requirement check.
  """

  name: str
  optional: bool
  result: CheckResult


@dataclasses.dataclass(frozen=True, slots=True)
class OracleReport:
  """Aggregated outcome of running multiple requirements.

  Attributes:
    ok: True if all non-optional requirements passed.
    errors: Outcomes for failed non-optional requirements.
    warnings: Outcomes for failed optional requirements.
    outcomes: Outcomes for all requirements, in execution order.
  """

  ok: bool
  errors: tuple[RequirementOutcome, ...] = ()
  warnings: tuple[RequirementOutcome, ...] = ()
  outcomes: tuple[RequirementOutcome, ...] = ()


@dataclasses.dataclass(frozen=True, slots=True, kw_only=True)
class BaseRequirement(abc.ABC):
  """Abstract base class for a single benchmark preparation requirement.

  Attributes:
    name: Human-readable requirement name for logs and reports.
    optional: Whether failure should be treated as a warning instead of an error.
  """

  name: str
  optional: bool = False

  @abc.abstractmethod
  def check(self, ctx: BenchmarkContext) -> utils.CheckResult:
    """Evaluates the requirement."""
    raise NotImplementedError


# ----------------------------
# Logging helpers
# ----------------------------


@dataclasses.dataclass(frozen=True, slots=True)
class LoggerConfig:
  """Configuration for the bundle logger.

  Attributes:
    root_name: Root logger name for the bundle.
    logs_dir: Directory for log files (if configured/used).
    console_level: Logging level for console output.
    root_level: Logging level for the root logger.
  """

  root_name: str
  logs_dir: pathlib.Path = pathlib.Path("logs")
  console_level: int = logging.INFO
  root_level: int = logging.DEBUG


def truncate_text(text: str, max_chars: int, *, suffix: str = "...") -> str:
  """Truncates text to at most max_chars characters."""
  if len(text) <= max_chars:
    return text
  return text[:max_chars] + suffix


def log_result_details(logger: logging.Logger, result: CheckResult) -> None:
  """Logs extra details for a CheckResult (used when verbose = True)."""
  if result.cwd is not None:
    logger.info("   cwd: %s", result.cwd)
  if result.returncode is not None:
    logger.info("   returncode: %s", result.returncode)
  if result.timed_out:
    logger.info("   timed_out: True")

  if result.stdout:
    logger.info(
        "   stdout:\n%s",
        truncate_text(result.stdout, DEFAULT_MAX_TRUNCATED_MESSAGE_CHARS))
  if result.stderr:
    logger.info(
        "   stderr:\n%s",
        truncate_text(result.stderr, DEFAULT_MAX_TRUNCATED_MESSAGE_CHARS))


def _is_console_handler(h: logging.Handler) -> bool:
  """Checks if a logging handler targets the standard console output."""
  return (
      isinstance(h, logging.StreamHandler)
      and not isinstance(h, logging.FileHandler)
      and getattr(h, "stream", None) in (sys.stdout, sys.stderr)
  )


def get_logger(config: LoggerConfig,
               *,
               component: str | None = None) -> logging.Logger:
  """Returns a configured logger (optionally namespaced for a component)."""
  config.logs_dir.mkdir(parents=True, exist_ok=True)

  root = logging.getLogger(config.root_name)
  root.setLevel(config.root_level)
  root.propagate = False  # Avoid double logging via the root logger

  # Add handlers once
  if not any(_is_console_handler(h) for h in root.handlers):
    console_handler = logging.StreamHandler()
    console_handler.setLevel(config.console_level)
    console_handler.setFormatter(
        logging.Formatter(_LOG_FORMAT, datefmt=_DATE_FORMAT))
    root.addHandler(console_handler)

  if component:
    return root.getChild(component)
  return root


# ----------------------------
# Oracles report helpers
# ----------------------------


class _RequirementLike(typing.Protocol):
  """Structural type for objects treated as requirements by the oracle logic.

  Attributes:
    name: Requirement name.
    optional: Whether this requirement is optional.
  """

  name: str
  optional: bool


ReqT = typing.TypeVar("ReqT", bound=_RequirementLike)


def build_oracle_report(
    *,
    logger: logging.Logger,
    requirements_fn: Callable[[], Sequence[ReqT]],
    check_fn: Callable[[ReqT], CheckResult],
) -> OracleReport:
  """Executes requirements and returns a structured OracleReport."""
  errors: list[RequirementOutcome] = []
  warnings: list[RequirementOutcome] = []
  outcomes: list[RequirementOutcome] = []

  try:
    requirements = list(requirements_fn())
  except Exception:
    logger.exception("Failed to build requirements")
    outcome = RequirementOutcome(
        name="requirements",
        optional=False,
        result=CheckResult.failure("failed to build requirements"),
    )
    return OracleReport(ok=False, errors=(outcome,), outcomes=(outcome,))

  for req in requirements:
    try:
      result = check_fn(req)
    except Exception as exc:
      logger.exception("Requirement raised: %s", req.name)
      result = CheckResult.failure(f"exception during check: {exc}")

    outcome = RequirementOutcome(name=req.name,
                                 optional=req.optional,
                                 result=result)
    outcomes.append(outcome)

    if result.ok:
      continue
    if req.optional:
      warnings.append(outcome)
    else:
      errors.append(outcome)

  return OracleReport(
      ok=not errors,
      errors=tuple(errors),
      warnings=tuple(warnings),
      outcomes=tuple(outcomes),
  )


def log_oracle_report(
    logger: logging.Logger,
    *,
    label: str,
    report: OracleReport,
    verbose: bool = False,
) -> bool:
  """Logs a PASS/FAIL summary for an oracle report and returns report.ok."""
  if not report.ok:
    logger.info("%s: FAIL", label)
    for out in report.errors:
      logger.error(" - %s: %s", out.name, out.result.message)
      if verbose:
        log_result_details(logger, out.result)
    for out in report.warnings:
      logger.warning(" - %s: %s", out.name, out.result.message)
      if verbose:
        log_result_details(logger, out.result)
    return False

  if report.warnings:
    logger.info("%s: PASS (with warnings)", label)
    for out in report.warnings:
      logger.warning(" - %s: %s", out.name, out.result.message)
      if verbose:
        log_result_details(logger, out.result)
  else:
    logger.info("%s: PASS", label)

  return True


def record_result(
    results: MutableMapping[str, int],
    name: str,
    ok: bool,
) -> int:
  """Records a pass/fail result and returns the numeric score contribution."""
  score = 1 if ok else 0
  results[name] = score
  return score


# ----------------------------
# Misc helpers
# ----------------------------


def decode_text(value: object | None) -> str:
  """Decpdes subprocess output typing.fields to text."""
  if value is None:
    return ""
  if isinstance(value, bytes):
    return value.decode(errors="replace")
  return str(value)


def to_path(value: object) -> pathlib.Path:
  """Normalizes a path-like value to a Path object."""
  if isinstance(value, pathlib.Path):
    return value
  if isinstance(value, (str, os.PathLike)):
    return pathlib.Path(value)
  raise TypeError(f"Value cannot be interpreted as a path: {type(value)!r}")
