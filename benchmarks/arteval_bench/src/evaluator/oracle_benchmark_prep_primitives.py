"""Benchmark preparation oracle primitives.

This module provides:
  1. Requirement types to specify benchmark-bundle prerequisites (tools, repo
     state, expected files).
  2. An orchestrator base class that runs checks, logs results, and returns a
     pass/fail outcome.

Derived oracles typically only override requirements() to declare a list of
preparation requirements (paths, commands, and optional output signatures) to
validate, but they can customize how checks are constructed if needed.
"""

from __future__ import annotations

import abc
import dataclasses
import logging
import os
import pathlib
import shlex
import subprocess
import types
import codecs
import locale
import selectors
import time

from collections.abc import Mapping, Sequence

from evaluator import utils


# ------------------------------------------------------------------------------
# Basic types and constants
# ------------------------------------------------------------------------------


_CommandT = str | Sequence[str]


# ------------------------------------------------------------------------------
# Helper functions
# ------------------------------------------------------------------------------


def _format_command(cmd: _CommandT, *, use_shell: bool) -> str:
  """Returns a readable representation of command suitable for error messages."""
  if isinstance(cmd, str):
    return cmd if use_shell else shlex.quote(cmd)
  # NOTE: quote() used for readability display only
  return " ".join(shlex.quote(str(arg)) for arg in cmd)


def _cwd_suffix(cwd: pathlib.Path | None) -> str:
  """Formats cwd as an error-message suffix."""
  if cwd is None:
    return ""
  return f" [cwd = {cwd}]"


def _missing_path_error(path: pathlib.Path) -> str | None:
  """Returns an error message if a required path does not exist."""
  if not path.exists():
    return f"path missing: {path}"
  return None


def _run_command(
    *,
    cmd: _CommandT,
    cwd: pathlib.Path | None,
    timeout_seconds: float,
    env_overrides: Mapping[str, str],
    use_shell: bool,
    signature: str | None,
) -> utils.CheckResult:
  """Runs a command and returns a utils.CheckResult.

  Signature matching is done against raw (untruncated) stdout/stderr to avoid
  false negatives, while stdout/stderr stored in the result are truncated to
  bounded size for logging.
  """
  env = None
  if env_overrides:
    env = os.environ.copy()
    for k, v in env_overrides.items():
      if k is None or str(k) == "":
        return utils.CheckResult.failure(
            f"invalid env var name in overrides: {k!r}{_cwd_suffix(cwd)}",
            stdout="",
            stderr="",
            returncode=None,
            timed_out=False,
            cwd=cwd,
        )
      env[str(k)] = str(v)

  cmd_display = _format_command(cmd, use_shell=use_shell)
  cwd_note = _cwd_suffix(cwd)

  cmd_run: str | Sequence[str]
  if use_shell and not isinstance(cmd, str):
    cmd_run = _format_command(cmd, use_shell=True)
  else:
    cmd_run = cmd

  max_chars = utils.DEFAULT_MAX_CAPTURE_CHARS
  suffix = "..."

  def _append_bounded(buf: list[str], cur_len: int, text: str) -> tuple[int, bool]:
    """Append up to max_chars, return (new_len, overflowed)."""
    if cur_len >= max_chars:
      return cur_len, True
    remaining = max_chars - cur_len
    if len(text) <= remaining:
      buf.append(text)
      return cur_len + len(text), False
    buf.append(text[:remaining])
    return max_chars, True

  sig = signature if (signature is not None and signature.strip()) else None
  sig_found_stdout = (sig is None)
  sig_found_stderr = (sig is None)
  k = 0 if sig is None else max(len(sig) - 1, 0)

  stdout_tail = ""
  stderr_tail = ""
  stderr_head = "" 

  encoding = locale.getpreferredencoding(False) or "utf-8"
  stdout_dec = codecs.getincrementaldecoder(encoding)(errors="replace")
  stderr_dec = codecs.getincrementaldecoder(encoding)(errors="replace")

  try:
    proc = subprocess.Popen(
        cmd_run,
        cwd=cwd,
        env=env,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        shell=use_shell,
        text=False,  # bytes, decode incrementally
    )
  except OSError as exc:
    return utils.CheckResult.failure(
        f"failed to run command: {cmd_display}{cwd_note}: {exc}",
        stdout="",
        stderr=str(exc),
        returncode=None,
        timed_out=False,
        cwd=cwd,
    )

  assert proc.stdout is not None
  assert proc.stderr is not None

  sel = selectors.DefaultSelector()
  sel.register(proc.stdout, selectors.EVENT_READ, data="stdout")
  sel.register(proc.stderr, selectors.EVENT_READ, data="stderr")

  stdout_parts: list[str] = []
  stderr_parts: list[str] = []
  stdout_len = 0
  stderr_len = 0
  stdout_overflow = False
  stderr_overflow = False

  deadline = time.monotonic() + float(timeout_seconds)

  def _read_chunk(stream) -> bytes:
    if hasattr(stream, "read1"):
      return stream.read1(8192)
    return stream.read(8192)

  timed_out = False

  while sel.get_map():
    remaining = deadline - time.monotonic()
    if remaining <= 0:
      timed_out = True
      break

    for key, _mask in sel.select(timeout=min(0.25, remaining)):
      stream = key.fileobj
      chunk = _read_chunk(stream)
      if not chunk:
        try:
          sel.unregister(stream)
        except Exception:
          pass
        try:
          stream.close()
        except Exception:
          pass
        continue

      if key.data == "stdout":
        text = stdout_dec.decode(chunk)
        stdout_len, ov = _append_bounded(stdout_parts, stdout_len, text)
        stdout_overflow = stdout_overflow or ov
        if sig is not None and not sig_found_stdout:
          hay = stdout_tail + text
          if sig in hay:
            sig_found_stdout = True
          stdout_tail = hay[-k:] if k else ""
      else:
        text = stderr_dec.decode(chunk)
        stderr_len, ov = _append_bounded(stderr_parts, stderr_len, text)
        stderr_overflow = stderr_overflow or ov
        if sig is not None and not sig_found_stderr:
          hay = stderr_tail + text
          if sig in hay:
            sig_found_stderr = True
          stderr_tail = hay[-k:] if k else ""
        if sig is not None and k and len(stderr_head) < k:
          need = k - len(stderr_head)
          stderr_head += text[:need]

  if timed_out:
    try:
      proc.kill()
    except Exception:
      pass
    try:
      proc.wait(timeout=5.0)
    except Exception:
      pass

    stdout = "".join(stdout_parts) + (suffix if stdout_overflow else "")
    stderr = "".join(stderr_parts) + (suffix if stderr_overflow else "")

    return utils.CheckResult.failure(
        f"command timed out after {timeout_seconds}s: {cmd_display}{cwd_note}",
        stdout=stdout,
        stderr=stderr,
        returncode=None,
        timed_out=True,
        cwd=cwd,
    )

  try:
    proc.wait(timeout=5.0)
  except Exception:
    pass

  stdout = "".join(stdout_parts) + (suffix if stdout_overflow else "")
  stderr = "".join(stderr_parts) + (suffix if stderr_overflow else "")

  if proc.returncode != 0:
    return utils.CheckResult.failure(
        f"command failed (rc = {proc.returncode}): {cmd_display}{cwd_note}",
        stdout=stdout,
        stderr=stderr,
        returncode=proc.returncode,
        timed_out=False,
        cwd=cwd,
    )

  if sig is not None:
    if not (sig_found_stdout or sig_found_stderr):
      boundary = stdout_tail + "\n" + stderr_head
      if sig not in boundary:
        return utils.CheckResult.failure(
            f"signature not found: {sig!r}: {cmd_display}{cwd_note}",
            stdout=stdout,
            stderr=stderr,
            returncode=proc.returncode,
            timed_out=False,
            cwd=cwd,
        )

  return utils.CheckResult.success(
      stdout=stdout,
      stderr=stderr,
      returncode=proc.returncode,
      cwd=cwd,
  )


# ------------------------------------------------------------------------------
# Oracle's core logic
# ------------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True, slots=True)
class BenchmarkContext:
  """Context passed to benchmark preparation requirements.

  Attributes:
    logger: Logger for diagnostics and shared policies.
  """

  logger: logging.Logger


@dataclasses.dataclass(frozen=True, slots=True, kw_only=True)
class FailRequirement(utils.BaseRequirement):
  """A requirement that always fails with a fixed message.

  Attributes:
    name: Human-readable requirement name for logs and reports.
    optional: Whether failure should be treated as a warning instead of an error.
    message: Failure message to report.
  """

  message: str

  def check(self, _ctx: BenchmarkContext) -> utils.CheckResult:
    return utils.CheckResult.failure(self.message)


@dataclasses.dataclass(frozen=True, slots=True, kw_only=True)
class BenchmarkRequirement(utils.BaseRequirement):
  """Validates an optional filesystem path and optionally runs a command.

  Attributes:
    name: Human-readable requirement name for logs and reports.
    optional: Whether failure should be treated as a warning instead of an error.
    filepath: Optional path that must exist; also influences working directory.
    cmd: Optional command to execute (argv tokens preferred; string only with shell).
    signature: Optional substring that must appear in raw stdout or stderr.
    timeout_seconds: Timeout for the command, in seconds.
    env_overrides: Environment variables to override for the subprocess.
    use_shell: Whether to execute the command through the shell.
  """

  filepath: pathlib.Path | str | os.PathLike[str] | None = None
  cmd: _CommandT | None = None
  signature: str | None = None
  timeout_seconds: float = 5.0
  env_overrides: Mapping[str, str] = dataclasses.field(default_factory=dict)
  use_shell: bool = False

  def __post_init__(self) -> None:
    if not self.name:
      raise ValueError("BenchmarkRequirement.name must be non-empty")

    if self.filepath is not None and not isinstance(self.filepath,
                                                    pathlib.Path):
      object.__setattr__(self, "filepath", utils.to_path(self.filepath))

    if isinstance(self.cmd, (list, tuple)):
      if not self.cmd:
        raise ValueError(f"{self.name}: cmd must be non-empty")
      object.__setattr__(self, "cmd", tuple(self.cmd))
    elif isinstance(self.cmd, str):
      if not self.cmd.strip():
        raise ValueError(f"{self.name}: cmd must be non-empty")
      if not self.use_shell:
        raise ValueError(
            f"{self.name}: string cmd requires use_shell = True (prefer argv tokens)"
        )
    elif self.cmd is None:
      pass
    else:
      raise TypeError(
          f"{self.name}: cmd must be a string or a sequence of args")

    if self.cmd is None and self.filepath is None:
      raise ValueError(
          f"{self.name}: must specify at least one of cmd or filepath")

    if self.timeout_seconds <= 0:
      raise ValueError(f"{self.name}: timeout_seconds must be > 0")

    if self.signature is not None and not self.signature.strip():
      object.__setattr__(self, "signature", None)

    object.__setattr__(self, "env_overrides",
                       types.MappingProxyType(dict(self.env_overrides)))

  def check(self, _ctx: BenchmarkContext) -> utils.CheckResult:
    cwd: pathlib.Path | None = None
    if self.filepath is not None:
      assert isinstance(self.filepath, pathlib.Path)
      error = _missing_path_error(self.filepath)
      if error is not None:
        return utils.CheckResult.failure(error, cwd=None)

      cwd = self.filepath if self.filepath.is_dir() else self.filepath.parent

    # If no command is provided, treat this requirement as a pure path check
    if self.cmd is None:
      return utils.CheckResult.success(cwd=cwd)

    return _run_command(
        cmd=self.cmd,
        cwd=cwd,
        timeout_seconds=self.timeout_seconds,
        env_overrides=self.env_overrides,
        use_shell=self.use_shell,
        signature=self.signature,
    )


class OracleBenchmarkPrepBase(abc.ABC):
  """Base class for a benchmark preparation oracle.

  Derived classes typically implement requirements() to declare preparation checks.

  Attributes:
    _logger: Logger used for reporting and diagnostics.
  """

  _ORACLE_NAME = "BenchmarkPrep"

  def __init__(self, *, logger: logging.Logger) -> None:
    self._logger = logger

  @abc.abstractmethod
  def requirements(self) -> Sequence[utils.BaseRequirement]:
    """Returns an ordered list of requirements to validate."""
    raise NotImplementedError

  def report(self) -> utils.OracleReport:
    """Executes requirements and returns a structured report."""
    ctx = BenchmarkContext(logger=self._logger)
    return utils.build_oracle_report(
        logger=self._logger,
        requirements_fn=self.requirements,
        check_fn=lambda req: req.check(ctx),
    )

  def run(self, *, verbose: bool = False) -> bool:
    """Returns True iff all required checks pass (logs results)."""
    rep = self.report()
    return utils.log_oracle_report(self._logger,
                                   label=self._ORACLE_NAME,
                                   report=rep,
                                   verbose=verbose)
