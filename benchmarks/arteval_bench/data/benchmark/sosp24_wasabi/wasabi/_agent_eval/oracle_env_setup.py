#!/usr/bin/env python3
"""
Environment Setup Checker (configurable & pythonic)

- Repository: branch/remote checks
- Prerequisites: driven by a declarative DEPENDENCIES table
- Paths: WASABI_ROOT_DIR and JAVA_HOME

Change versions or add tools by editing DEPENDENCIES below.
"""
import os
import sys
import re
import shutil
import subprocess
from dataclasses import dataclass
from typing import Iterable, Optional, Tuple
from pathlib import Path

# ---------------------- Constants ----------------------
HOME = Path.home()
REPO_DIR = HOME / "sosp24-ae" / "wasabi"
EXPECTED_REMOTE_SUBSTR = "github.com/bastoica/wasabi"
EXPECTED_BRANCH = "sosp24-ae"
EXPECTED_WASABI_ROOT = str(REPO_DIR)
EXPECTED_JAVA_HOME = "/usr/lib/jvm/java-8-openjdk-amd64/jre"

SUCCESS_CODE = 0
FAIL_CODE = 255

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

def run(cmd: Iterable[str]) -> Tuple[int, str, str]:
  """
  Run a command and return (rc, stdout, stderr) tuple.
  """
  try:
    cp = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    return cp.returncode, cp.stdout or "", cp.stderr or ""
  except FileNotFoundError:
    return 127, "", ""

def parse_version_tuple(text: str) -> VersionTuple:
  """
  Extract the first version-like token from arbitrary text.
  For example, for Java: '1.8.0_422' -> (1, 8, 0)
  """
  m = re.search(r"(\d+(?:\.\d+){0,3})", text)
  return tuple(int(x) for x in m.group(1).split(".")) if m else ()

def extract_version(text: str, pattern: str) -> Tuple[VersionTuple, str]:
  """
  Apply regex pattern on a version string.
  """
  m = re.search(pattern, text, re.I)
  if not m:
    return (), "unknown"
  ver_str = m.group(1)
  return parse_version_tuple(ver_str), ver_str

def cmp_versions(found: VersionTuple, required: VersionTuple, mode: str) -> bool:
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

def repo_check():
  if not REPO_DIR.exists():
    return False, "repo path missing"

  r = subprocess.run(["git", "-C", str(REPO_DIR), "rev-parse", "--is-inside-work-tree"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
  if r.returncode != 0 or r.stdout.strip() != "true":
    return False, "not a git repo"

  r = subprocess.run(["git", "-C", str(REPO_DIR), "rev-parse", "--abbrev-ref", "HEAD"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
  if r.returncode != 0 or r.stdout.strip() != EXPECTED_BRANCH:
    return False, f"wrong branch (got '{(r.stdout or '').strip()}')"

  r = subprocess.run(["git", "-C", str(REPO_DIR), "remote", "-v"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
  if r.returncode != 0 or EXPECTED_REMOTE_SUBSTR not in r.stdout:
    return False, "remote not pointing to bastoica/wasabi"
  return True, ""

def paths_check():
  wasabi_root = os.environ.get("WASABI_ROOT_DIR", "")
  if not (wasabi_root == EXPECTED_WASABI_ROOT and Path(wasabi_root).exists()):
    return False, "WASABI_ROOT_DIR incorrect"
  java_home = os.environ.get("JAVA_HOME", "")
  if not (java_home == EXPECTED_JAVA_HOME and Path(java_home).exists()):
    return False, "JAVA_HOME incorrect"
  return True, ""

def check_dependency(dep: Dependency) -> Optional[str]:
  """
  Core method that checks whether a certain dependency of a version 
  equal or greather than that specified in the README is installed.
  """
  if shutil.which(dep.binary) is None:
    return f"{dep.name} missing"


  if dep.cmd is None and dep.parse_regex is None and dep.require is None:
    return None

  rc, out, err = run(dep.cmd or [])
  text = (out + "\n" + err).strip()

  if dep.parse_regex and dep.require and dep.compare:
    ver_tuple, ver_str = extract_version(text, dep.parse_regex)
    if not ver_tuple:
      return f"{dep.name} version unreadable"
    ok = cmp_versions(ver_tuple, dep.require, dep.compare)
    cmp_word = "==" if dep.compare == "eq" else ">="
    want = ".".join(map(str, dep.require))
    return None if ok else f"{dep.name} {cmp_word} {want} not met (got {ver_str})"

  return f"{dep.name} check misconfigured"

def prereqs_check():
  problems: list[str] = []
  for dep in DEPENDENCIES:
    msg = check_dependency(dep)
    if msg:
      problems.append(msg)
  if problems:
    return False, "; ".join(problems)
  return True, ""

def main():
  results = []

  ok, why = repo_check()
  print(f"Repository: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
  results.append(ok)

  ok, why = prereqs_check()
  print(f"Prerequisites: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
  results.append(ok)

  ok, why = paths_check()
  print(f"Paths: {'PASS' if ok else 'FAIL' + (' - ' + why if why else '')}")
  results.append(ok)

  sys.exit(SUCCESS_CODE if all(results) else FAIL_CODE)

if __name__ == "__main__":
  main()
