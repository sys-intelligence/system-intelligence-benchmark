#!/usr/bin/env python3
import sys
import subprocess
from pathlib import Path

from utils import REPO_DIRS, logger


class OracleBenchmarkPrep:

  def __init__(self):
    self.repo_root = Path(REPO_DIRS["acto"])
    self.expected_remote = "https://github.com/xlab-uiuc/acto.git"
    self.expected_branch = "anvil-dev"

  def run_shell_command(self, cmd):
    """
    Run a command and return (rc, stdout, stderr) tuple.
    """
    try:
      cp = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
      return cp.returncode, (cp.stdout or "").strip(), (cp.stderr or "").strip()
    except FileNotFoundError as e:
      return 127, "", str(e)

  def check_repo_exists(self):
    """
    Check that repository root exists and is a git working tree.
    """
    if not self.repo_root.is_dir():
      return False, f"acto: FAIL (repo) - directory not found: {self.repo_root}"

    rc, out, err = self.run_shell_command(
      ["git", "-C", str(self.repo_root), "rev-parse", "--is-inside-work-tree"]
    )
    if rc != 0 or out != "true":
      return False, f"acto: FAIL (repo) - not a git working tree: {err or out}"

    return True, "acto: PASS (repo) - git working tree present"

  def check_remote_origin(self):
    """
    Check that <origin> remote matches the expected repository URL.
    """
    rc, out, err = self.run_shell_command(
      ["git", "-C", str(self.repo_root), "remote", "get-url", "origin"]
    )
    if rc != 0:
      return False, f"acto: FAIL (remote) - cannot read origin remote: {err or out}"

    origin_url = (out or "").strip()
    def normalize(url: str) -> str:
      return url[:-4] if url.endswith(".git") else url

    if normalize(origin_url) != normalize(self.expected_remote):
      return False, (
        "acto: FAIL (remote) - origin URL "
        f"{origin_url!r} does not match expected {self.expected_remote!r}"
      )

    return True, f"acto: PASS (remote) - origin URL matches {self.expected_remote}"

  def check_branch_and_head(self):
    """
    Check that the current branch is the expected one and that the current 
    commit resolves to a valid hash.
    """
    rc, out, err = self.run_shell_command(
      ["git", "-C", str(self.repo_root), "rev-parse", "--abbrev-ref", "HEAD"]
    )
    if rc != 0:
      return False, f"acto: FAIL (branch) - cannot read current branch: {err or out}"

    branch = (out or "").strip()
    if branch != self.expected_branch:
      return False, f"acto: FAIL (branch) - {branch!r} != expected {self.expected_branch!r}"

    rc, out, err = self.run_shell_command(
      ["git", "-C", str(self.repo_root), "rev-parse", "HEAD"]
    )
    if rc != 0:
      return False, f"acto: FAIL (commit) - cannot read HEAD: {err or out}"

    head = (out or "").strip()
    if not head:
      return False, "acto: FAIL (commit) - empty HEAD hash"

    return True, f"acto: PASS (branch/commit) - {branch}@{head[:12]}"

  def check_submodules_recursive(self):
    """
    Check that submodules (if any) are initialized, approximating a --recursive clone.
    """
    gitmodules = self.repo_root / ".gitmodules"
    if not gitmodules.exists():
      # No submodules configured; nothing to check
      return True, "acto: PASS (submodules) - no submodules configured"

    rc, out, err = self.run_shell_command(
      ["git", "-C", str(self.repo_root), "submodule", "status", "--recursive"]
    )
    if rc != 0:
      return False, f"acto: FAIL (submodules) - git submodule status failed: {err or out}"

    # Heuristic: lines starting with '-' indicate uninitialized submodules
    uninitialized = [line for line in out.splitlines() if line.startswith("-")]
    if uninitialized:
      return False, (
        "acto: FAIL (submodules) - uninitialized submodules present "
        "(clone may have been done without --recursive)"
      )

    return True, "acto: PASS (submodules) - all submodules initialized"

  def run(self):
    """
    Run all repository checks and return True on overall success.
    """
    results: list[bool] = []

    ok, msg = self.check_repo_exists()
    logger.info(msg)
    results.append(ok)

    ok, msg = self.check_remote_origin()
    logger.info(msg)
    results.append(ok)

    ok, msg = self.check_branch_and_head()
    logger.info(msg)
    results.append(ok)

    ok, msg = self.check_submodules_recursive()
    logger.info(msg)
    results.append(ok)

    if all(results):
      return True

    return False