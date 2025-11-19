#!/usr/bin/env python3
import os
import re
import shutil
import subprocess
from dataclasses import dataclass
from typing import Iterable, Optional, Tuple
from pathlib import Path

from utils import REPO_DIR
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

  Dependency(
    name="git", binary="git"
  ),

  Dependency(
    name="maven", binary="mvn",
    cmd=["mvn", "-v"], parse_regex=r"Apache Maven\s+([0-9.]+)",
    require=(3, 6, 3), compare="gte",
  ),
  Dependency(
    name="gradle", binary="gradle",
    cmd=["gradle", "-v"], parse_regex=r"Gradle\s+([0-9.]+)",
    require=(4, 4, 1), compare="gte",
  ),
  Dependency(
    name="ant", binary="ant",
    cmd=["ant", "-version"], parse_regex=r"version\s+([0-9.]+)",
    require=(1, 10), compare="gte",
  ),
  Dependency(
    name="python3", binary="python3",
    cmd=["python3", "--version"], parse_regex=r"Python\s+([0-9.]+)",
    require=(3, 10), compare="gte",
  ),
  Dependency(
    name="java", binary="java",
    cmd=["java", "-version"], parse_regex=r'version\s+"([^"]+)"',
    require=(1, 8), compare="eq",
  ),
]

class OracleEnvSetup:

  def __init__(self) -> None:
    self.expected_root_dir = REPO_DIR
    self.expected_java_hone = "/usr/lib/jvm/java-8-openjdk-amd64/jre"

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
    Compare versions either to match exactly ('eq') 
    or the installed version is greather than the reference one ('gte').
    """
    if not found:
      return False
    f, r = list(found), list(required)
    while len(f) < len(r): f.append(0)
    while len(r) < len(f): r.append(0)
    return (f == r) if mode == "eq" else (f >= r)

  def paths_check(self):
    wasabi_root = os.environ.get("WASABI_ROOT_DIR", "")
    if not (wasabi_root == self.expected_root_dir and Path(wasabi_root).exists()):
      return False, "WASABI_ROOT_DIR incorrect"
    java_home = os.environ.get("JAVA_HOME", "")
    if not (java_home == self.expected_java_home and Path(java_home).exists()):
      return False, "JAVA_HOME incorrect"
    return True, ""

  def check_dependency(self, dep: Dependency) -> Optional[str]:
    """
    Core method that checks whether a certain dependency of a version 
    equal or greather than that specified in the README is installed.
    """
    if shutil.which(dep.binary) is None:
      return f"{dep.name} missing"


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
