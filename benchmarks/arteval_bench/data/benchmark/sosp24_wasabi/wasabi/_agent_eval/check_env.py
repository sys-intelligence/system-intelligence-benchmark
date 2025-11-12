#!/usr/bin/env python3
import os
import sys
import shutil
import subprocess
from pathlib import Path

HOME = Path.home()
REPO_DIR = HOME / "sosp24-ae" / "wasabi"
EXPECTED_REMOTE_SUBSTR = "github.com/bastoica/wasabi"
EXPECTED_BRANCH = "sosp24-ae"
EXPECTED_WASABI_ROOT = str(REPO_DIR)
EXPECTED_JAVA_HOME = "/usr/lib/jvm/java-8-openjdk-amd64/jre"

PREREQS = ["tree", "mvn", "gradle", "ant", "python3", "java", "git"]

def repo_check():
    # path exists
    if not REPO_DIR.exists():
        return False, "repo path missing"
    # git repo
    r = subprocess.run(["git", "-C", str(REPO_DIR), "rev-parse", "--is-inside-work-tree"],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if r.returncode != 0 or r.stdout.strip() != "true":
        return False, "not a git repo"
    # correct branch
    r = subprocess.run(["git", "-C", str(REPO_DIR), "rev-parse", "--abbrev-ref", "HEAD"],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if r.returncode != 0 or r.stdout.strip() != EXPECTED_BRANCH:
        return False, f"wrong branch (got '{(r.stdout or '').strip()}')"
    # correct remote
    r = subprocess.run(["git", "-C", str(REPO_DIR), "remote", "-v"],
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    if r.returncode != 0 or EXPECTED_REMOTE_SUBSTR not in r.stdout:
        return False, "remote not pointing to bastoica/wasabi"
    return True, ""

def prereqs_check():
    missing = [cmd for cmd in PREREQS if shutil.which(cmd) is None]
    if missing:
        return False, f"missing: {', '.join(missing)}"
    return True, ""

def paths_check():
    wasabi_root = os.environ.get("WASABI_ROOT_DIR", "")
    if not (wasabi_root == EXPECTED_WASABI_ROOT and Path(wasabi_root).exists()):
        return False, "WASABI_ROOT_DIR incorrect"
    java_home = os.environ.get("JAVA_HOME", "")
    if not (java_home == EXPECTED_JAVA_HOME and Path(java_home).exists()):
        return False, "JAVA_HOME incorrect"
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

    sys.exit(0 if all(results) else 1)

if __name__ == "__main__":
    main()

