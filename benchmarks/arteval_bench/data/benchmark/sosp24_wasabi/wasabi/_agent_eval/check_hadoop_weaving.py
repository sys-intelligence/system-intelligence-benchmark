#!/usr/bin/env python3
import sys
import shlex
import subprocess
from pathlib import Path

# --- Config: adjust if your tree lives elsewhere ---
HADOOP_DIR = Path.home() / "sosp24-ae" / "benchmarks" / "hadoop"
MAX_CLASS_DIRS = 200          # safety cap; 0 means no cap
MAX_CLASSES_PER_DIR = 2000    # safety cap per classes/ dir; 0 means no cap
ASPECTJ_MARKERS = [
    # Synthetic members commonly injected by ajc
    "ajc$preClinit",
    "ajc$initFailureCause",
    "ajc$tjp",                 # JoinPoint static part fields
    "ajc$before$",             # woven advice methods
    "ajc$after$",
    "ajc$around$",
    "ajc$interField$",         # inter-type field stubs
    "ajc$interMethod$",        # inter-type method stubs

    # Runtime references that appear in woven bytecode
    "org.aspectj.runtime.reflect.Factory",
    "org.aspectj.runtime.internal.AroundClosure",
    "org.aspectj.lang.JoinPoint",
    "org.aspectj.lang.JoinPoint$StaticPart",
    "org.aspectj.lang.ProceedingJoinPoint",
    "org.aspectj.lang.Signature",
    "org.aspectj.lang.NoAspectBoundException",
]
# ---------------------------------------------------

def run(cmd):
    """Run a shell-safe command; return (rc, stdout, stderr)."""
    try:
        cp = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        return cp.returncode, (cp.stdout or "").strip(), (cp.stderr or "").strip()
    except FileNotFoundError as e:
        return 127, "", str(e)

def find_classes_dirs(root: Path):
    """Find all target/classes directories in the build tree."""
    cmd = ["bash", "-lc", f"shopt -s nullglob; find {shlex.quote(str(root))} -type d -path '*/target/classes' | sort"]
    rc, out, err = run(cmd)
    if rc != 0:
        return [], f"find failed: {err or out}"
    dirs = [Path(p) for p in out.splitlines() if p]
    return dirs, ""

def iter_class_files(classes_dir: Path, limit: int):
    """Yield up to `limit` .class files from a classes/ directory (recursive)."""
    # Use find for speed and to avoid Python recursion cost
    q = shlex.quote(str(classes_dir))
    cmd = ["bash", "-lc", f"shopt -s nullglob; find {q} -type f -name '*.class' | sort"]
    rc, out, err = run(cmd)
    if rc != 0 or not out:
        return []
    files = [Path(p) for p in out.splitlines() if p]
    if limit and len(files) > limit:
        # sample evenly
        step = max(len(files) // limit, 1)
        files = files[::step][:limit]
    return files

def classfile_has_aspect_markers(class_path: Path):
    """
    Stream a .class through `strings` and search for AspectJ markers.
    Return (bool, matched_marker_or_empty).
    """
    pattern = "|".join(ASPECTJ_MARKERS)
    cmd = ["bash", "-lc", f"strings {shlex.quote(str(class_path))} | grep -a -E '{pattern}' -m 1"]
    rc, out, err = run(cmd)
    if rc == 0 and out:
        # Return the first matched marker token if possible
        matched = next((m for m in ASPECTJ_MARKERS if m in out), out)
        return True, matched
    return False, ""

def main():
    if not HADOOP_DIR.is_dir():
        print(f"Weaving (class scan): FAIL - Hadoop directory not found: {HADOOP_DIR}")
        sys.exit(2)

    class_dirs, err = find_classes_dirs(HADOOP_DIR)
    if not class_dirs:
        print(f"Weaving (class scan): FAIL - no target/classes directories found under {HADOOP_DIR}")
        sys.exit(1)

    if MAX_CLASS_DIRS and len(class_dirs) > MAX_CLASS_DIRS:
        class_dirs = class_dirs[:MAX_CLASS_DIRS]

    for cdir in class_dirs:
        class_files = iter_class_files(cdir, MAX_CLASSES_PER_DIR)
        for cf in class_files:
            ok, marker = classfile_has_aspect_markers(cf)
            if ok:
                print(f"Weaving (class scan): PASS - marker '{marker}' in {cf}")
                sys.exit(0)

    print("Weaving (class scan): FAIL - scanned .class files but found no AspectJ markers (ajc$…/org.aspectj…)")
    sys.exit(1)

if __name__ == "__main__":
    main()

