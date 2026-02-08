#!/usr/bin/env python3
import shlex
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List

from evaluator.oracle_benchmark_prep_primitives import (
  OracleBenchmarkPrepBase,
  BenchmarkRequirement,
)
from evaluator import utils


def _required_path(paths, key: str, *, label: str) -> Path:
  """Returns a required path from a mapping with a clear error."""
  try:
    return utils.to_path(paths[key])
  except KeyError as e:
    raise ValueError(f"Missing {label}[{key!r}] in EntryConfig") from e


def _required_meta(meta: Dict[str, Any], key: str, *, label: str) -> Any:
  """Returns a required metadata value with a clear error."""
  try:
    return meta[key]
  except KeyError as e:
    raise ValueError(f"Missing {label}[{key!r}] in EntryConfig.metadata") from e


def _as_dict(x: Any) -> Dict[str, Any]:
  if isinstance(x, dict):
    return x
  raise ValueError(f"Expected dict in EntryConfig.metadata, got: {type(x)!r}")


def _as_list_str(x: Any) -> List[str]:
  if isinstance(x, list) and all(isinstance(v, str) for v in x):
    return x
  raise ValueError("Expected list[str] in EntryConfig.metadata")


@dataclass(frozen=True, slots=True)
class _WeavingRequirement:
  name: str
  oracle: "OracleBenchmarkPrep"
  app: str
  app_root: Path
  optional: bool = False

  def check(self, ctx) -> utils.CheckResult:
    ok, msg = self.oracle.check_app_weaving(self.app, self.app_root)
    ctx.logger.info(msg)
    return utils.CheckResult.success(cwd=self.app_root) if ok else utils.CheckResult.failure(msg, cwd=self.app_root)


class OracleBenchmarkPrep(OracleBenchmarkPrepBase):

  def __init__(self, *, config: utils.EntryConfig, logger):
    super().__init__(logger=logger)
    self._config = config

    meta = _as_dict(getattr(config, "metadata", {}) or {})

    self._bench_specs = _as_dict(_required_meta(meta, "benchmarks", label="metadata"))
    self._weaving_plugin_sig = str(_required_meta(meta, "weaving_plugin_signature", label="metadata"))
    self._aspectj_markers = _as_list_str(_required_meta(meta, "aspectj_markers", label="metadata"))

    # Bounds for the max number of compiled classes checked for instrumentation markers
    self.max_class_dirs = int(meta.get("max_class_dirs", 200))
    self.max_classess_per_dir = int(meta.get("max_classess_per_dir", 2000))

  def requirements(self) -> tuple[object, ...]:
    bench_root = _required_path(self._config.repository_paths, "benchmarks", label="repository_paths")
    wasabi_root = _required_path(self._config.repository_paths, "sosp24-wasabi", label="repository_paths")

    reqs: List[object] = []

    for app in sorted(self._bench_specs.keys()):
      spec = _as_dict(self._bench_specs[app])

      app_root = bench_root / app
      expected_commit = str(_required_meta(spec, "commit", label=f"metadata.benchmarks[{app}]"))
      pom_file = str(_required_meta(spec, "pom_file", label=f"metadata.benchmarks[{app}]"))
      pom_backup = str(_required_meta(spec, "pom_backup", label=f"metadata.benchmarks[{app}]"))

      reqs.append(
        BenchmarkRequirement(
          name=f"{app}: clone",
          filepath=app_root,
          cmd=["git", "-C", str(app_root), "rev-parse", "HEAD"],
          signature=expected_commit,
          timeout_seconds=10.0,
        )
      )

      q_pom = shlex.quote(pom_file)
      q_backup = shlex.quote(pom_backup)
      q_sig = shlex.quote(self._weaving_plugin_sig)

      reqs.append(
        BenchmarkRequirement(
          name=f"{app}: pom swap",
          filepath=app_root,
          cmd=[
            "bash", "-lc",
            (
              "set -euo pipefail; "
              f"test -f {q_pom}; "
              f"test -f {q_backup}; "
              f"! cmp -s {q_pom} {q_backup}; "
              f"grep -a -F -q {q_sig} {q_pom}; "
              "echo POM_SWAP_OK"
            ),
          ],
          signature="POM_SWAP_OK",
          timeout_seconds=10.0,
          use_shell=False,
        )
      )

      reqs.append(
        BenchmarkRequirement(
          name=f"{app}: weaving config",
          filepath=app_root,
          cmd=[
            "cat", "pom.xml",
          ],
          signature=self._weaving_plugin_sig,
          timeout_seconds=120.0,
        )
      )

      reqs.append(
        _WeavingRequirement(
          name=f"{app}: weaving",
          oracle=self,
          app=app,
          app_root=app_root,
        )
      )

    return tuple(reqs)

  def run_shell_command(self, cmd):
    """
    Run a bash command given as argument.
    """
    try:
      cp = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
      return cp.returncode, (cp.stdout or "").strip(), (cp.stderr or "").strip()
    except FileNotFoundError as e:
      return 127, "", str(e)

  def find_class_dirs(self, app_root: Path):
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
    rc, out, err = self.run_shell_command(cmd)
    if rc != 0:
      return [], f"find failed: {err or out}"
    dirs = [Path(p) for p in out.splitlines() if p]
    return dirs, ""

  def iter_class_files(self, classes_dir: Path, limit: int):
    """
    Iterate over .class files from a class directory, processing up to
    a configurable number of files.
    """
    q = shlex.quote(str(classes_dir))
    cmd = ["bash", "-lc", f"shopt -s nullglob; find {q} -type f -name '*.class' | sort"]
    rc, out, err = self.run_shell_command(cmd)
    if rc != 0 or not out:
      return []
    files = [Path(p) for p in out.splitlines() if p]
    if limit and len(files) > limit:
      step = max(len(files) // limit, 1)
      files = files[::step][:limit]
    return files

  def classfile_has_aspect_markers(self, class_path: Path):
    """
    Search through a decoded .class for AspectJ markers.
    """
    qfile = shlex.quote(str(class_path))
    e_args = " ".join(f"-e {shlex.quote(m)}" for m in self._aspectj_markers)
    cmd = ["bash", "-lc", f"strings {qfile} | grep -a -F -m 1 {e_args}"]
    rc, out, err = self.run_shell_command(cmd)
    if rc == 0 and out:
      matched = next((m for m in self._aspectj_markers if m in out), out)
      return True, matched
    return False, ""

  def check_app_weaving(self, app: str, app_root: Path):
    """
    Scan compiled .class files for AspectJ markers.
    """
    if not app_root.is_dir():
      return False, f"{app}: FAIL (waving) - directory not found: {app_root}"

    class_dirs, err = self.find_class_dirs(app_root)
    if err:
      return False, f"{app}: FAIL (waving) - {err}"
    if not class_dirs:
      return False, f"{app}: FAIL (waving) - no compiled .class files found under {app_root}"

    dirs = class_dirs[:self.max_class_dirs] if (self.max_class_dirs and len(class_dirs) > self.max_class_dirs) else class_dirs

    for cdir in dirs:
      for cf in self.iter_class_files(cdir, self.max_classess_per_dir):
        ok, marker = self.classfile_has_aspect_markers(cf)
        if ok:
          return True, f"{app}: PASS (weaving) - marker '{marker}' in {cf}"

    return False, f"{app}: FAIL (weaving) - scanned .class files but found no AspectJ markers"
