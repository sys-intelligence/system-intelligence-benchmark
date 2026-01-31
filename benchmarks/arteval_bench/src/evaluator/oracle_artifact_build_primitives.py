"""Artifact build oracle primitives.

This module provides:
  1. Requirement types to specify build commands.
  2. An orchestrator base class that runs build checks, logs results, and returns
     a pass/fail outcome.

Derived oracles typically only override requirements() to declare a list of build
requirements to run, but they can customize command execution policies or logging
behavior if needed.
"""

from __future__ import annotations

import abc
import dataclasses
import logging
import os
import pathlib
import subprocess
import types
import selectors
import time

from collections.abc import Mapping, Sequence

from evaluator import utils


# ------------------------------------------------------------------------------
# Helper functions
# ------------------------------------------------------------------------------


def _summarize_process_output(stdout: str, stderr: str) -> str:
  """Combines and truncates process output to keep messages readable."""
  out = stdout.strip()
  err = stderr.strip()
  if out and err:
    combined = f"stdout:\n{out}\n\nstderr:\n{err}"
  else:
    combined = out or err
  return utils.truncate_text(combined,
                             utils.DEFAULT_MAX_TRUNCATED_MESSAGE_CHARS)


def _require_directory(path: pathlib.Path, *, label: str) -> str | None:
  """Returns an error message if path is not an existing directory."""
  if not path.exists():
    return f"{label} missing: {path}"
  if not path.is_dir():
    return f"{label} is not a directory: {path}"
  return None


# ------------------------------------------------------------------------------
# Oracle's core logic
# ------------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True, slots=True)
class BuildContext:
  """Context passed to build requirements.

  Attributes:
    logger: Logger for diagnostics and shared policies.
  """

  logger: logging.Logger



@dataclasses.dataclass(frozen=True, slots=True, kw_only=True)
class BuildCommandRequirement(utils.BaseRequirement):
  """Runs a build command within a working directory.

  Attributes:
    name: Human-readable requirement name for logs and reports.
    optional: Whether failure should be treated as a warning instead of an error.
    cwd: Base working directory.
    command: Command argv to execute.
    relative_workdir: Optional subdirectory within cwd used as the actual workdir.
    timeout_seconds: Timeout for the command, in seconds.
    env_overrides: Environment variables to override for the subprocess.
  """

  cwd: pathlib.Path
  command: Sequence[str]
  relative_workdir: pathlib.Path | None = None
  timeout_seconds: float = 60.0
  env_overrides: Mapping[str, str] = dataclasses.field(default_factory=dict)

  def __post_init__(self) -> None:
    object.__setattr__(self, "cwd", utils.to_path(self.cwd))
    if self.relative_workdir is not None:
      object.__setattr__(self, "relative_workdir", utils.to_path(self.relative_workdir))

    if isinstance(self.command, (str, bytes)):
      raise TypeError(f"{self.name}: command must be a sequence of argv strings, not a single string/bytes")

    if not self.command:
      raise ValueError(f"{self.name}: command must be non-empty")

    bad = [a for a in self.command if not isinstance(a, str) or a == ""]
    if bad:
      raise TypeError(f"{self.name}: all command argv entries must be non-empty str; bad entries: {bad!r}")

    if self.timeout_seconds <= 0:
      raise ValueError(f"{self.name}: timeout (seconds) must be > 0")

    # NOTE: Be tolerant to callers passing non-str values (e.g., Path/int) by
    # normalizing everything to str, since subprocess env requires str->str.
    env_dict_raw = dict(self.env_overrides)
    env_dict: dict[str, str] = {}
    for k, v in env_dict_raw.items():
      # Preserve previous strictness for obviously broken keys.
      if k is None or k == "":
        raise TypeError(f"{self.name}: env_overrides contains an empty env var name: {k!r}")
      env_dict[str(k)] = str(v)

    # Prevent obvious "not relative" cases early.
    if self.relative_workdir is not None and self.relative_workdir.is_absolute():
      raise ValueError(f"{self.name}: relative_workdir must be a relative path, got: {self.relative_workdir}")

    object.__setattr__(self, "command", tuple(self.command))
    object.__setattr__(self, "env_overrides", types.MappingProxyType(env_dict))

  @staticmethod
  def _is_within_base_dir(*, base: pathlib.Path, target: pathlib.Path) -> bool:
    """Returns True iff target is within base (after resolving symlinks).

    Assumes both paths exist (caller should validate directories first).
    """
    try:
      base_real = base.resolve(strict=True)
      target_real = target.resolve(strict=True)

      # NOTE: Prefer pathlib semantics over string commonpath to avoid
      # platform corner cases (drives, separators). This also avoids false
      # positives from simple string-prefix checks.
      try:
        target_real.relative_to(base_real)
        return True
      except ValueError:
        return False
    except OSError:
      return False

  @staticmethod
  def _coerce_text(x: object) -> str:
    # NOTE: utils.decode_text may not accept str in some codebases. This helper
    # safely handles bytes/str/None and keeps the old behavior stable.
    if x is None:
      return ""
    if isinstance(x, str):
      return x
    if isinstance(x, (bytes, bytearray, memoryview)):
      return utils.decode_text(bytes(x))
    # Fallback: best-effort stringification
    return str(x)

  def _run_with_limited_output(
    self,
    *,
    workdir: pathlib.Path,
    env: Mapping[str, str],
  ) -> tuple[int | None, str, str, bool]:
    """Run process while limiting captured output to avoid unbounded memory.

    Returns (returncode, stdout, stderr, timed_out).
    """
    # NOTE: We run with stdout/stderr pipes in *binary* mode and decode ourselves.
    # This avoids UnicodeDecodeError surprises while reading incrementally.
    try:
      proc = subprocess.Popen(
        self.command,
        cwd=workdir,
        env=dict(env),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=False,
      )
    except OSError as exc:
      # Let caller map this to CheckResult.failure, preserving existing behavior.
      raise

    assert proc.stdout is not None
    assert proc.stderr is not None

    sel = selectors.DefaultSelector()
    sel.register(proc.stdout, selectors.EVENT_READ, data="stdout")
    sel.register(proc.stderr, selectors.EVENT_READ, data="stderr")

    # NOTE: Cap memory usage by storing only up to a fixed number of bytes.
    # We use 4x char cap as a conservative UTF-8 upper bound.
    byte_cap = int(utils.DEFAULT_MAX_CAPTURE_CHARS) * 4

    stdout_buf = bytearray()
    stderr_buf = bytearray()

    deadline = time.monotonic() + float(self.timeout_seconds)
    timed_out = False

    def _read_chunk(stream) -> bytes:
      # Prefer read1 when available for buffered streams.
      if hasattr(stream, "read1"):
        return stream.read1(8192)  # type: ignore[attr-defined]
      return stream.read(8192)

    # Read incrementally from both pipes until closed or timeout.
    while sel.get_map():
      remaining = deadline - time.monotonic()
      if remaining <= 0:
        timed_out = True
        break

      events = sel.select(timeout=min(0.25, remaining))
      for key, _mask in events:
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
          if len(stdout_buf) < byte_cap:
            take = min(len(chunk), byte_cap - len(stdout_buf))
            stdout_buf.extend(chunk[:take])
          # NOTE: Discard remainder to cap memory; continue draining to avoid deadlock.
        else:
          if len(stderr_buf) < byte_cap:
            take = min(len(chunk), byte_cap - len(stderr_buf))
            stderr_buf.extend(chunk[:take])

    if timed_out:
      try:
        proc.kill()
      except Exception:
        pass

      # Best-effort drain for a short period so we capture some tail output
      # without risking hangs.
      drain_deadline = time.monotonic() + 1.0
      while sel.get_map() and time.monotonic() < drain_deadline:
        events = sel.select(timeout=0.1)
        for key, _mask in events:
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
            if len(stdout_buf) < byte_cap:
              take = min(len(chunk), byte_cap - len(stdout_buf))
              stdout_buf.extend(chunk[:take])
          else:
            if len(stderr_buf) < byte_cap:
              take = min(len(chunk), byte_cap - len(stderr_buf))
              stderr_buf.extend(chunk[:take])

      # Reap the process to avoid zombies.
      try:
        proc.wait(timeout=5.0)
      except Exception:
        pass

      stdout = utils.truncate_text(self._coerce_text(stdout_buf), utils.DEFAULT_MAX_CAPTURE_CHARS)
      stderr = utils.truncate_text(self._coerce_text(stderr_buf), utils.DEFAULT_MAX_CAPTURE_CHARS)
      return None, stdout, stderr, True

    # Process finished or pipes closed; reap returncode.
    try:
      rc = proc.wait(timeout=5.0)
    except Exception:
      # If something odd happens, keep behavior conservative.
      rc = proc.returncode

    stdout = utils.truncate_text(self._coerce_text(stdout_buf), utils.DEFAULT_MAX_CAPTURE_CHARS)
    stderr = utils.truncate_text(self._coerce_text(stderr_buf), utils.DEFAULT_MAX_CAPTURE_CHARS)
    return rc, stdout, stderr, False

  def check(self, ctx: BuildContext) -> utils.CheckResult:
    del ctx  # Deliberetly reserved for future extensions

    error = _require_directory(self.cwd, label="working directory")
    if error is not None:
      return utils.CheckResult.failure(error, cwd=self.cwd)

    workdir = self.cwd
    if self.relative_workdir is not None:
      workdir = self.cwd / self.relative_workdir
      error = _require_directory(workdir, label="working directory")
      if error is not None:
        return utils.CheckResult.failure(error, cwd=workdir)

      # Walidate cwd and prevent ``espacping'' (e.g., ../ or symlinks)
      if not self._is_within_base_dir(base=self.cwd, target=workdir):
        return utils.CheckResult.failure(
          f"working directory escapes base cwd: base={self.cwd} workdir={workdir}",
          cwd=workdir,
        )

    env = os.environ.copy()
    if self.env_overrides:
      env.update(self.env_overrides)

    try:
      # NOTE: Avoid capture_output=True because it can buffer unbounded output
      # and spike memory; we capture incrementally with a fixed cap.
      returncode, stdout, stderr, timed_out = self._run_with_limited_output(
        workdir=workdir,
        env=env,
      )
    except OSError as exc:
      return utils.CheckResult.failure(
        f"failed to run command: {exc}",
        stdout="",
        stderr=str(exc),
        returncode=None,
        timed_out=False,
        cwd=workdir,
      )

    if timed_out:
      # Handle case when stdout/stderr is None
      return utils.CheckResult.failure(
        f"command timed out after {self.timeout_seconds}s",
        stdout=stdout,
        stderr=stderr,
        returncode=None,
        timed_out=True,
        cwd=workdir,
      )

    if returncode != 0:
      detail = _summarize_process_output(stdout, stderr)
      msg = f"command failed (rc = {returncode})"
      if detail:
        msg = f"{msg}: {detail}"
      return utils.CheckResult.failure(
        msg,
        stdout=stdout,
        stderr=stderr,
        returncode=returncode,
        timed_out=False,
        cwd=workdir,
      )

    return utils.CheckResult.success(
      stdout=stdout,
      stderr=stderr,
      returncode=returncode,
      cwd=workdir,
    )


class OracleArtifactBuildBase(abc.ABC):
  """Base class for an artifact build oracle.

  Derived classes typically implement requirements() to declare build checks.

  Attributes:
    _logger: Logger used for reporting and diagnostics.
  """

  _ORACLE_NAME = "ArtifactBuild"

  def __init__(self, *, logger: logging.Logger) -> None:
    self._logger = logger

  @abc.abstractmethod
  def requirements(self) -> Sequence[utils.BaseRequirement]:
    """Returns an ordered list of build requirements to validate."""
    raise NotImplementedError

  def report(self) -> utils.OracleReport:
    """Executes requirements and returns a structured report."""
    ctx = BuildContext(logger=self._logger)
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
