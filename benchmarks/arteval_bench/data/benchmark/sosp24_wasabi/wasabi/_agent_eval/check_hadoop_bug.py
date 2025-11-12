#!/usr/bin/env python3
import os
import sys
import subprocess
from pathlib import Path
from collections import deque
from typing import List, Tuple, Optional

# ---------------- Configuration ----------------
TIMEOUT = 60 * 60  # seconds; adjust if your tests take longer

HADOOP_DIR = Path.home() / "sosp24-ae" / "benchmarks" / "hadoop"
CONFIG_FILE = Path.home() / "sosp24-ae" / "wasabi" / "wasabi-testing" / "config" / "hadoop" / "example.conf"
TEST_NAME = "TestFSEditLogLoader"

ERROR_PATTERN = "NullPointerException"
BEFORE_CONTEXT = 2
AFTER_CONTEXT = 10
# ------------------------------------------------


def run_command_with_timeout(cmd: List[str], dir_path: str):
    """
    Run a command with a timeout of {TIMEOUT} seconds.

    Parameters:
      cmd (list): The command to run as a list of arguments.

    Returns:
      subprocess.CompletedProcess | None: The result of the command execution, or None if timed out.
    """
    try:
        # capture_output=True -> stdout/stderr are bytes; we decode later
        result = subprocess.run(cmd, cwd=dir_path, shell=False, capture_output=True, timeout=TIMEOUT)
        return result
    except subprocess.TimeoutExpired:
        return None


def build_maven_surefire_cmd(config_file: Path, test_name: str) -> List[str]:
    """Construct the surefire command exactly as in the README (without tee/log)."""
    return [
        "mvn", "surefire:test",
        "-fn", "-B",
        f"-DconfigFile={str(config_file)}",
        f"-Dtest={test_name}",
    ]


def decode_output(cp: subprocess.CompletedProcess) -> List[str]:
    """Decode combined stdout+stderr to a list of text lines (no trailing newlines)."""
    # Combine, prefer preserving original order? We can concatenate; Maven lines are mostly on stdout.
    stdout = cp.stdout or b""
    stderr = cp.stderr or b""
    text = stdout + b"\n" + stderr
    return text.decode(errors="replace").splitlines()


def scan_lines_for_pattern(
    lines: List[str],
    pattern: str,
    before_ctx: int,
    after_ctx: int
) -> Tuple[bool, List[str]]:
    """
    Scan lines line-by-line for `pattern`, returning (found, context_block).

    Context block emulates `grep -B{before_ctx} -A{after_ctx}` for the *first* match.
    """
    before = deque(maxlen=before_ctx)
    after_remaining = 0
    context: List[str] = []

    for idx, line in enumerate(lines):
        if after_remaining > 0:
            context.append(line)
            after_remaining -= 1
            if after_remaining == 0:
                break  # done collecting after-context

        if pattern in line:
            # capture before-context
            context.extend(list(before))
            # the matched line itself (print just the pattern like grep, or the full line?)
            # README's example shows just the word "NullPointerException" on its own line.
            # To be faithful, insert the pattern token as its own line:
            context.append(pattern)
            # then after-context
            after_remaining = after_ctx

        before.append(line)

    found = any(pattern == l for l in context)
    return found, context


def validate_paths() -> Optional[str]:
    """Ensure required paths exist; return error message if not."""
    if not HADOOP_DIR.is_dir():
        return f"Hadoop directory not found: {HADOOP_DIR}"
    if not CONFIG_FILE.is_file():
        return f"Config file not found: {CONFIG_FILE}"
    return None


def main():
    # Basic path sanity
    path_err = validate_paths()
    if path_err:
        print(f"RunCheck: FAIL - {path_err}")
        sys.exit(2)

    cmd = build_maven_surefire_cmd(CONFIG_FILE, TEST_NAME)

    # Execute with timeout, capture output in-memory (no log file)
    result = run_command_with_timeout(cmd, str(HADOOP_DIR))
    if result is None:
        print(f"RunCheck: FAIL - command timed out after {TIMEOUT} seconds")
        sys.exit(2)

    # Decode and scan line-by-line (no saved logfile)
    lines = decode_output(result)
    found, ctx = scan_lines_for_pattern(lines, ERROR_PATTERN, BEFORE_CONTEXT, AFTER_CONTEXT)

    if found:
        print("RunCheck: PASS - NullPointerException detected")
        if BEFORE_CONTEXT or AFTER_CONTEXT:
            print("---- Context ----")
            for l in ctx:
                print(l)
            print("---- End Context ----")
        sys.exit(0)
    else:
        print("RunCheck: FAIL - NullPointerException NOT detected")
        sys.exit(1)


if __name__ == "__main__":
    main()

