#!/usr/bin/env python3
import subprocess
import re
from dataclasses import dataclass
from typing import Iterable, Optional, Tuple
from pathlib import Path

from utils import logger


Version = Tuple[int, int, int]


@dataclass(frozen=True)
class ToolRequirement:
  name: str
  cmd: list[str]
  min_version: Optional[Version] = None
  optional: bool = False


MIN_RUST_VERSION: Version = (1, 78, 0)


TOOL_REQUIREMENTS: list[ToolRequirement] = [
  ToolRequirement(
    name="rustc",
    cmd=["rustc", "--version"],
    min_version=MIN_RUST_VERSION,
  ),
  ToolRequirement(
    name="cargo",
    cmd=["cargo", "--version"],
  ),
  ToolRequirement(
    name="node",
    cmd=["node", "--version"],
  ),
  ToolRequirement(
    name="make",
    cmd=["make", "--version"],
    optional=True,
  ),
]


class OracleEnvSetup:

  def run_shell_command(
    self,
    cmd: Iterable[str],
    cwd: Optional[Path] = None,
  ) -> Tuple[int, str, str]:
    """
    Run a command and return (rc, stdout, stderr) tuple.
    """
    try:
      cp = subprocess.run(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        cwd=str(cwd) if cwd is not None else None,
      )
      return cp.returncode, cp.stdout or "", cp.stderr or ""
    except FileNotFoundError:
      return 127, "", ""

  def parse_version(self, s: str) -> Optional[Version]:
    """
    Extract a version number from a string.
    """
    m = re.search(r"(?:^|\s)v?(\d+)\.(\d+)(?:\.(\d+))?", s)
    if not m:
      return None
    major = int(m.group(1))
    minor = int(m.group(2))
    patch = int(m.group(3)) if m.group(3) is not None else 0
    return (major, minor, patch)

  def version_lt(self, a: Version, b: Version) -> bool:
    return a < b

  def check_tool(self, req: ToolRequirement) -> Tuple[Optional[str], Optional[str]]:
    """
    Check a single dependency requirement, including version.
    """
    rc, out, err = self.run_shell_command(req.cmd)
    combined = (out + "\n" + err).strip()

    if rc == 127:
      if req.optional:
        return None, f"{req.name} missing (optional)"
      return f"{req.name} not found", None

    if rc != 0:
      if req.optional:
        return None, f"{req.name} check failed (rc={rc}) (optional)"
      return f"{req.name} check failed (rc={rc})", None

    if req.min_version is not None:
      v = self.parse_version(combined)
      if v is None:
        return f"{req.name} version parse failed", None
      if self.version_lt(v, req.min_version):
        return f"{req.name} too old (need >= {req.min_version[0]}.{req.min_version[1]}.{req.min_version[2]})", None

    return None, None

  def build_check(self):
    """
    Validate required dependnecies and environment setup.
    """
    problems: list[str] = []
    warnings: list[str] = []

    for req in TOOL_REQUIREMENTS:
      problem, warning = self.check_tool(req)
      if problem:
        problems.append(problem)
      if warning:
        warnings.append(warning)

    if problems:
      return False, "; ".join(problems)

    if warnings:
      return True, "WARN: " + "; ".join(warnings)

    return True, ""

  def run(self):
    ok, why = self.build_check()
    label = "Environment"
    if ok and why:
      logger.info(f"{label}: PASS - {why}")
      return ok
    logger.info(f"{label}: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
    return ok