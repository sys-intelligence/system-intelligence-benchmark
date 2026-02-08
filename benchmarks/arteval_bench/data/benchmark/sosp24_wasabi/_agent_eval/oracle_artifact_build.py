#!/usr/bin/env python3
import dataclasses
import fnmatch
import hashlib
import logging
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import Any, Dict, List, Tuple

from evaluator.oracle_artifact_build_primitives import OracleArtifactBuildBase
from evaluator.utils import EntryConfig
from evaluator import utils


def _required_path(paths: Dict[str, Path], key: str, *, label: str) -> Path:
  """Returns a required path from a mapping with a clear error."""
  try:
    p = paths[key]
  except KeyError as e:
    raise ValueError(f"Missing {label}[{key!r}] in EntryConfig") from e
  return utils.to_path(p)


def _required_meta(meta: Dict[str, Any], key: str, *, label: str) -> Any:
  """Returns a required metadata value with a clear error."""
  try:
    return meta[key]
  except KeyError as e:
    raise ValueError(f"Missing {label}[{key!r}] in EntryConfig.metadata") from e


def _sha256(path: Path) -> str:
  h = hashlib.sha256()
  with path.open("rb") as f:
    for chunk in iter(lambda: f.read(1024 * 1024), b""):
      h.update(chunk)
  return h.hexdigest()


def _pick_primary_jar(dir_path: Path, artifact_id: str, version: str) -> Path | None:
  """
  Picks a "primary" jar from a directory by matching artifactId/version while
  excluding common auxiliary jars (sources/javadoc/tests/original-*).
  """
  if not dir_path.is_dir():
    return None

  bad_tokens = ("-sources", "-javadoc", "-tests", "original-")
  pattern = f"{artifact_id}-{version}*.jar"
  cands = [
      p for p in dir_path.glob("*.jar")
      if p.is_file() and fnmatch.fnmatch(p.name, pattern) and not any(tok in p.name for tok in bad_tokens)
  ]
  if not cands:
    return None

  # Prefer newest (best-effort)
  return max(cands, key=lambda p: p.stat().st_mtime)


def _strip_ns(tag: str) -> str:
  return tag.split("}", 1)[-1]


@dataclasses.dataclass(frozen=True, slots=True)
class _BuildInputsRequirement:
  name: str
  oracle: "OracleArtifactBuild"
  optional: bool = False

  def check(self, ctx) -> utils.CheckResult:
    repo_dir = self.oracle.repo_dir
    if not repo_dir.exists() or not repo_dir.is_dir():
      ctx.logger.info("Build: FAIL - base project directory not found")
      return utils.CheckResult.failure("base project directory not found", cwd=repo_dir)

    poms = self.oracle.find_poms(repo_dir)
    if not poms:
      ctx.logger.info("Build: FAIL - no pom.xml files found under repo")
      return utils.CheckResult.failure("no pom.xml files found under repo", cwd=repo_dir)

    root_pom = repo_dir / "pom.xml"
    top_defaults: Dict[str, str] = {}
    if root_pom.exists():
      root_mod = self.oracle.parse_pom(root_pom, top_defaults=None)
      if not root_mod.get("error"):
        if root_mod.get("groupId"):
          top_defaults["groupId"] = root_mod["groupId"]
        if root_mod.get("version"):
          top_defaults["version"] = root_mod["version"]

    modules: List[Dict[str, Any]] = []
    errors: List[Tuple[Path, str]] = []
    for pom in poms:
      m = self.oracle.parse_pom(pom, top_defaults=top_defaults)
      if m.get("error"):
        errors.append((pom, m["error"]))
        continue
      if not all([m.get("artifactId"), m.get("groupId"), m.get("version")]):
        errors.append((pom, "missing groupId/artifactId/version after inheritance"))
      else:
        modules.append(m)

    if errors:
      ctx.logger.info("Build: FAIL - POM parsing errors present")
      for pom, err in errors[:5]:
        ctx.logger.info(f" - {pom}: {err}")
      if len(errors) > 5:
        ctx.logger.info(f" ... {len(errors)-5} more")
      return utils.CheckResult.failure("POM parsing errors present", cwd=repo_dir)

    self.oracle._modules = modules
    return utils.CheckResult.success(cwd=repo_dir)


@dataclasses.dataclass(frozen=True, slots=True)
class _PrimaryModuleBuildRequirement:
  name: str
  oracle: "OracleArtifactBuild"
  optional: bool = False

  def check(self, ctx) -> utils.CheckResult:
    modules = getattr(self.oracle, "_modules", None)
    if not modules:
      return utils.CheckResult.failure("modules not initialized", cwd=self.oracle.repo_dir)

    selector = self.oracle.primary_artifact_selector.strip()
    if ":" in selector:
      want_gid, want_aid = selector.split(":", 1)
      want_gid = want_gid.strip()
      want_aid = want_aid.strip()
    else:
      want_gid, want_aid = "", selector.strip()

    chosen = None
    for m in modules:
      gid = (m.get("groupId") or "").strip()
      aid = (m.get("artifactId") or "").strip()
      if not aid:
        continue
      if want_gid:
        if gid == want_gid and aid == want_aid:
          chosen = m
          break
      else:
        if aid == want_aid:
          chosen = m
          break

    if not chosen:
      return utils.CheckResult.failure(
        f"primary module not found for selector {selector!r}",
        cwd=self.oracle.repo_dir,
      )

    packaging = (chosen.get("packaging") or "jar").strip()
    if packaging == "pom":
      ctx.logger.info("Code build: FAIL")
      return utils.CheckResult.failure("primary module resolved to packaging=pom", cwd=Path(chosen["dir"]))

    gid = (chosen.get("groupId") or "").strip()
    aid = (chosen.get("artifactId") or "").strip()
    ver = (chosen.get("version") or "").strip()
    module_dir = Path(chosen["dir"])

    if not gid or not aid or not ver:
      return utils.CheckResult.failure(
        "primary module missing groupId/artifactId/version after inheritance",
        cwd=module_dir,
      )

    built = _pick_primary_jar(module_dir / "target", aid, ver)
    installed_dir = self.oracle.repo_path(gid, aid, ver)
    installed = _pick_primary_jar(installed_dir, aid, ver)

    if not built or not installed:
      ctx.logger.info("Code build: FAIL")
      if not built:
        ctx.logger.info(" Missing built JARs in target/:")
        ctx.logger.info(f"  - {module_dir}")
      if not installed:
        ctx.logger.info(" Missing artifacts in local Maven repository:")
        ctx.logger.info(f"  - {gid}:{aid}:{ver}")
      return utils.CheckResult.failure("missing built jar and/or installed artifact", cwd=module_dir)

    hb = _sha256(built)
    hi = _sha256(installed)
    if hb != hi:
      ctx.logger.info("Code build: FAIL")
      detail = f"built={built} sha256={hb}\ninstalled={installed} sha256={hi}"
      return utils.CheckResult.failure(
        "primary artifact mismatch: target/ jar does not match local Maven repo jar",
        stdout=utils.truncate_text(detail, utils.DEFAULT_MAX_CAPTURE_CHARS),
        cwd=module_dir,
      )

    ctx.logger.info("Code build: PASS")
    return utils.CheckResult.success(cwd=module_dir)


class OracleArtifactBuild(OracleArtifactBuildBase):
  def __init__(self, *, config: EntryConfig, logger: logging.Logger):
    super().__init__(logger=logger)
    self._config = config

    self.repo_dir = _required_path(config.repository_paths, "sosp24-wasabi", label="repository_paths").resolve()
    
    meta: Dict[str, Any] = getattr(config, "metadata", {}) or {}
    self.maven_packages_dir = utils.to_path(_required_meta(meta, "maven_repo_dir", label="metadata")).resolve()
    self.primary_artifact_selector = str(_required_meta(meta, "primary_artifact", label="metadata"))

    self._modules = None

  def requirements(self):
    return (
      _BuildInputsRequirement(name="Build", oracle=self),
      _PrimaryModuleBuildRequirement(name="Code build", oracle=self),
    )

  def xget(self, elem, tag):
    """
    Helper function to handle POM tags with or without default namespace
    """
    if elem is None:
      return None
    v = elem.find(tag)
    if v is not None and v.text:
      return v.text.strip()
    for child in elem:
      t = child.tag.split('}', 1)[-1]
      if t == tag:
        return (child.text or "").strip()
    return None

  def parse_pom(self, pom_path, top_defaults=None):
    """
    Collects POM files into dictionary <dir, pom, groupId, artifactId, vers, packaging>
    """
    try:
      tree = ET.parse(pom_path)
      root = tree.getroot()
    except Exception as e:
      return {"dir": pom_path.parent, "pom": pom_path, "error": f"XML parse error: {e}"}

    artifactId = self.xget(root, "artifactId")
    groupId = self.xget(root, "groupId")
    version = self.xget(root, "version")
    packaging = self.xget(root, "packaging") or "jar"

    parent = None
    for c in list(root):
      if _strip_ns(c.tag) == "parent":
        parent = c
        break

    if parent is not None:
      p_groupId = self.xget(parent, "groupId")
      p_version = self.xget(parent, "version")
      if not groupId and p_groupId:
        groupId = p_groupId
      if not version and p_version:
        version = p_version

    if top_defaults:
      groupId = groupId or top_defaults.get("groupId")
      version = version or top_defaults.get("version")

    return {
      "dir": pom_path.parent,
      "pom": pom_path,
      "groupId": groupId,
      "artifactId": artifactId,
      "version": version,
      "packaging": packaging
    }

  def find_poms(self, base):
    return sorted(base.rglob("pom.xml"))

  def repo_path(self, groupId, artifactId, version):
    parts = groupId.split(".")
    return self.maven_packages_dir.joinpath(*parts, artifactId, version)