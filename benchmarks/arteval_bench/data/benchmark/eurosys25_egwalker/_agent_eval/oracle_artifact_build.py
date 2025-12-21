#!/usr/bin/env python3
import os
import subprocess
from dataclasses import dataclass
from typing import Iterable, List, Optional, Tuple
from pathlib import Path

from utils import REPO_DIR
from utils import logger


@dataclass(frozen=True)
class BuildTarget:
  name: str
  repo_key: str
  cmd: List[str]


BUILD_TARGETS: List[BuildTarget] = [
  BuildTarget(
    name="artifact-core",
    repo_key="artifact-core",
    cmd=[
      "make",
      "-j8",
      "tools/diamond-types/target/release/dt",
      "tools/crdt-converter/target/release/crdt-converter",
      "tools/diamond-types/target/release/paper-stats",
      "tools/paper-benchmarks/target/memusage/paper-benchmarks",
      "tools/paper-benchmarks/target/release/paper-benchmarks",
      "tools/ot-bench/target/memusage/ot-bench",
      "tools/ot-bench/target/release/ot-bench"
    ],
  ),
]


class OracleArtifactBuild:

  def __init__(self) -> None:
    self.repo_dir = REPO_DIR

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

  def build_target(self, target: BuildTarget) -> Optional[str]:
    """
    Build a single target using its configured repository and command.
    """
    repo_path = Path(os.path.expanduser(self.repo_dir))
    if not repo_path.exists():
      return f"{target.name} repo directory missing"

    rc, out, err = self.run_shell_command(target.cmd, cwd=repo_path)
    if rc != 0:
      return f"{target.name} build failed (error code: {rc}; error message: {err})"

    return None

  def build_check(self):
    """
    Run builds for all configured targets and collect failures.
    """
    problems: List[str] = []
    for target in BUILD_TARGETS:
      msg = self.build_target(target)
      if msg:
        problems.append(msg)
    if problems:
      return False, "; ".join(problems)
    return True, ""

  def run(self):
    ok, why = self.build_check()
    logger.info(f"Build: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
    return ok