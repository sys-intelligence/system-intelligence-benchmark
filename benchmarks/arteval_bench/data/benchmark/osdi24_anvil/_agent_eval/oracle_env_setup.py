import os
import re
import shutil
import subprocess
from dataclasses import dataclass
from typing import Iterable, Optional, Tuple
from pathlib import Path

from utils import HOME, REPO_DIRS
from utils import logger

VersionTuple = Tuple[int, ...]


@dataclass(frozen=True)
class Dependency:
  name: str
  binary: str
  cmd: Optional[list] = None
  parse_regex: Optional[str] = None
  require: Optional[VersionTuple] = None
  compare: Optional[str] = None


DEPENDENCIES: list[Dependency] = [

  # Basic tooling
  Dependency(
    name="git", binary="git"
  ),

  # Docker, latest version is okay
  Dependency(
    name="docker", binary="docker",
  ),

  # Python v3.10+
  Dependency(
    name="python3", binary="python3",
    cmd=["python3", "--version"], parse_regex=r"Python\s+([0-9.]+)",
    require=(3, 10), compare="gte",
  ),

  # pip3 for Python 3.10+
  Dependency(
    name="pip3", binary="pip3",
  ),

  # Go toolchain (golang package), latest STL version
  Dependency(
    name="go", binary="go",
  ),

  # Kind v0.20.0
  Dependency(
    name="kind", binary="kind",
    cmd=["kind", "version"], parse_regex=r"v([0-9.]+)",
    require=(0, 20, 0), compare="gte",
  ),

  # Kubectl v1.22.9
  Dependency(
    name="kubectl", binary="kubectl",
    cmd=["kubectl", "version", "--client", "--short"],
    parse_regex=r"Client Version:\s+v?([0-9.]+)",
    require=(1, 22, 9), compare="gte",
  ),
]


class OracleEnvSetup:

  def __init__(self) -> None:
    # Root of the cloned repositories
    self.expected_root_dirs = REPO_DIRS.values()

    # Go paths that should be present in PATH
    self.go_root = HOME / "go"
    self.go_bin = self.go_root / "bin"

    # Python virtual environment inside the repo
    self.venv_dir = HOME / ".venv"

  def run_shell_command(self, cmd: Iterable[str]) -> Tuple[int, str, str]:
    """
    Run a command and return (rc, stdout, stderr) tuple.
    """
    try:
      cp = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
      return cp.returncode, cp.stdout or "", cp.stderr or ""
    except FileNotFoundError:
      return 127, "", ""

  def parse_version_tuple(self, text: str) -> VersionTuple:
    """
    Extract the first version-like token from arbitrary text.
    For example, for Java: '1.8.0_422' -> (1, 8, 0)
    """
    m = re.search(r"(\d+(?:\.\d+){0,3})", text)
    return tuple(int(x) for x in m.group(1).split(".")) if m else ()

  def extract_version(self, text: str, pattern: str) -> Tuple[VersionTuple, str]:
    """
    Apply regex pattern on a version string.
    """
    m = re.search(pattern, text, re.I)
    if not m:
      return (), "unknown"
    ver_str = m.group(1)
    return self.parse_version_tuple(ver_str), ver_str

  def cmp_versions(self, found: VersionTuple, required: VersionTuple, mode: str) -> bool:
    """
    Compare versions either to be greater or equal to the reference.
    """
    if not found:
      return False
    f, r = list(found), list(required)
    while len(f) < len(r):
      f.append(0)
    while len(r) < len(f):
      r.append(0)
    return (f == r) if mode == "eq" else (f >= r)

  def paths_check(self):
    """
    Check that Python virtual environment is succesfully created 
    and that Go-related paths are set properly.
    """
    problems: list[str] = []

    # Check repositories exist
    for dir in self.expected_root_dirs:
      if not Path(dir).exists():
        problems.append(f"{dir} directory not found repository not cloned properly")

    # Check Python virtual environment is created
    if not Path(self.venv_dir).exists():
      problems.append(".venv virtual environment missing (run 'python3 -m venv .venv')")

    # Check Go directories exit
    if not Path(self.go_root).exists():
      problems.append("$HOME/go directory missing (install golang and configure GOPATH)")
    if not Path(self.go_bin).exists():
      problems.append("$HOME/go/bin directory missing (ensure Go tools are installed)")

    # Check PATH contains Go path
    path_env = os.environ.get("PATH", "")
    go_root_str = str(self.go_root)
    go_bin_str = str(self.go_bin)
    if go_root_str not in path_env or go_bin_str not in path_env:
      problems.append("PATH missing $HOME/go or $HOME/go/bin "
                      "(export PATH=$HOME/go:$HOME/go/bin:$PATH)")

    if problems:
      return False, "; ".join(problems)
    return True, ""

  def check_dependency(self, dep: Dependency) -> Optional[str]:
    """
    Core method that checks whether a certain dependency of a version 
    equal or greather than a reference version is installed.
    """
    if shutil.which(dep.binary) is None:
      return f"{dep.name} missing"

    # If no version information is required, presence is enough
    if dep.cmd is None and dep.parse_regex is None and dep.require is None:
      return None

    rc, out, err = self.run_shell_command(dep.cmd or [])
    text = (out + "\n" + err).strip()

    if dep.parse_regex and dep.require and dep.compare:
      ver_tuple, ver_str = self.extract_version(text, dep.parse_regex)
      if not ver_tuple:
        return f"{dep.name} version unreadable"
      ok = self.cmp_versions(ver_tuple, dep.require, dep.compare)
      cmp_word = "==" if dep.compare == "eq" else ">="
      want = ".".join(map(str, dep.require))
      return None if ok else f"{dep.name} {cmp_word} {want} not met (got {ver_str})"

    return f"{dep.name} check misconfigured"

  def prereqs_check(self):
    problems: list[str] = []
    for dep in DEPENDENCIES:
      msg = self.check_dependency(dep)
      if msg:
        problems.append(msg)
    if problems:
      return False, "; ".join(problems)
    return True, ""

  def run(self):
    results = []

    ok, why = self.prereqs_check()
    logger.info(f"Prerequisites: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
    results.append(ok)

    ok, why = self.paths_check()
    logger.info(f"Paths: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
    results.append(ok)

    if all(results):
      return True

    return False