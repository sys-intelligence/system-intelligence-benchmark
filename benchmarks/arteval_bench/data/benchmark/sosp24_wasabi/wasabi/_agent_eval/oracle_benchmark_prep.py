#!/usr/bin/env python3
import sys
import shlex
import argparse
import subprocess
from pathlib import Path


BENCH_ROOT = Path.home() / "sosp24-ae" / "benchmarks"
REPOS = {
  "hadoop": ("https://github.com/apache/hadoop.git", "60867de"),
  "hbase": ("https://github.com/apache/hbase.git", "89ca7f4"),
  "hive": ("https://github.com/apache/hive.git", "e08a600"),
#  "cassandra": ("https://github.com/apache/cassandra.git", "f0ad7ea"),
#  "elasticsearch": ("https://github.com/elastic/elasticsearch.git", "5ce03f2"),
}

ASPECTJ_MARKERS = [
  "ajc$preClinit",
  "ajc$initFailureCause",
  "ajc$tjp",
  "ajc$before$",
  "ajc$after$",
  "ajc$around$",
  "ajc$interField$",
  "ajc$interMethod$",
  "org.aspectj.runtime.reflect.Factory",
  "org.aspectj.runtime.internal.AroundClosure",
  "org.aspectj.lang.JoinPoint",
  "org.aspectj.lang.JoinPoint$StaticPart",
  "org.aspectj.lang.ProceedingJoinPoint",
  "org.aspectj.lang.Signature",
  "org.aspectj.lang.NoAspectBoundException",
]

MAX_CLASS_DIRS = 200
MAX_CLASSES_PER_DIR = 2000

SUCCESS_CODE = 0
FAIL_CODE = 255

def run(cmd):
  """
  Run a bash command given as argument.
  """
  try:
    cp = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    return cp.returncode, (cp.stdout or "").strip(), (cp.stderr or "").strip()
  except FileNotFoundError as e:
    return 127, "", str(e)

def find_class_dirs(app_root: Path):
  """
  Find directories that contain .class files.
  """
  qroot = shlex.quote(str(app_root))
  cmd = [
    "bash",
    "-lc",
    (
      f"shopt -s nullglob; "
      f"find {qroot} -type f -name '*.class' "
      f"-not -path '*/.git/*' -not -path '*/.m2/*' -not -path '*/.gradle/*' "
      f"-printf '%h\n' | sort -u"
    ),
  ]
  rc, out, err = run(cmd)
  if rc != 0:
    return [], f"find failed: {err or out}"
  dirs = [Path(p) for p in out.splitlines() if p]
  return dirs, ""

def iter_class_files(classes_dir: Path, limit: int):
  """
  Iterate over .class files from a class directory, processing up to 
  a configurable number of files.
  """
  q = shlex.quote(str(classes_dir))
  cmd = ["bash", "-lc", f"shopt -s nullglob; find {q} -type f -name '*.class' | sort"]
  rc, out, err = run(cmd)
  if rc != 0 or not out:
    return []
  files = [Path(p) for p in out.splitlines() if p]
  if limit and len(files) > limit:
    step = max(len(files) // limit, 1)
    files = files[::step][:limit]
  return files

def check_repo_commit(app: str, app_root: Path, expected_commit_prefix: str):
  """
  Verify the repo at app_root is a git repo and HEAD matches an expected commit ID prefix.
  """
  if not app_root.is_dir():
    return False, f"{app}: FAIL - directory not found: {app_root}"

  rc, out, err = run(["git", "-C", str(app_root), "rev-parse", "HEAD"])
  if rc != 0:
    return False, f"{app}: FAIL - not a git repo or unreadable HEAD: {err or out}"

  head = (out or "").strip()
  if head.startswith(expected_commit_prefix):
    return True, f"{app}: PASS - commit {head[:12]} matches {expected_commit_prefix}"
  else:
    return False, f"{app}: FAIL - HEAD {head[:12]} != expected {expected_commit_prefix}*"


def classfile_has_aspect_markers(class_path: Path):
  """
  Search through a decoded .class for AspectJ markers.
  """
  pattern = "|".join(ASPECTJ_MARKERS)
  cmd = ["bash", "-lc", f"strings {shlex.quote(str(class_path))} | grep -a -E '{pattern}' -m 1"]
  rc, out, err = run(cmd)
  if rc == 0 and out:
    matched = next((m for m in ASPECTJ_MARKERS if m in out), out)
    return True, matched
  return False, ""

def check_app_weaving(app: str, app_root: Path):
  """
  Scan compiled .class files for AspectJ markers.
  """
  if not app_root.is_dir():
    return False, f"{app}: FAIL - directory not found: {app_root}"

  class_dirs, err = find_class_dirs(app_root)
  if err:
    return False, f"{app}: FAIL - {err}"
  if not class_dirs:
    return False, f"{app}: FAIL - no compiled .class files found under {app_root}"

  dirs = class_dirs[:MAX_CLASS_DIRS] if (MAX_CLASS_DIRS and len(class_dirs) > MAX_CLASS_DIRS) else class_dirs

  for cdir in dirs:
    for cf in iter_class_files(cdir, MAX_CLASSES_PER_DIR):
      ok, marker = classfile_has_aspect_markers(cf)
      if ok:
        return True, f"{app}: PASS - marker '{marker}' in {cf}"

  return False, f"{app}: FAIL - scanned .class files but found no AspectJ markers"


def main():
  success = True
  for app in REPOS:
    app_root = BENCH_ROOT / app
    
    expected_commit = REPOS[app][1]
    ok, msg = check_repo_commit(app, app_root, expected_commit)
    print(msg)
    success = success and ok
    print(success)

    ok, msg = check_app_weaving(app, app_root)
    print(msg)
    success = success and ok
    print(success)

  sys.exit(SUCCESS_CODE if success else FAIL_CODE)

if __name__ == "__main__":
  main()
