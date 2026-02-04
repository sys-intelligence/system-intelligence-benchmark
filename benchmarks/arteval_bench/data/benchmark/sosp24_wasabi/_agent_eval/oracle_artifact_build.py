#!/usr/bin/env python3
import xml.etree.ElementTree as ET
import fnmatch

from utils import HOME
from utils import REPO_DIR
from utils import logger

from evaluator.oracle_artifact_build_primitives import OracleArtifactBuildBase
from evaluator import utils


@dataclasses.dataclass(frozen=True, slots=True)
class _BuildInputsRequirement(utils.BaseRequirement):
  oracle: "OracleArtifactBuild"

  def check(self, ctx: object) -> utils.CheckResult:
    del ctx

    if not REPO_DIR.exists():
      logger.info("Build: FAIL - base project directory not found")
      return utils.CheckResult.failure("base project directory not found")

    poms = self.oracle.find_poms(REPO_DIR)
    if not poms:
      logger.info("Build: FAIL - no pom.xml files found under wasabi-testing")
      return utils.CheckResult.failure("no pom.xml files found under wasabi-testing")

    root_pom = REPO_DIR / "pom.xml"
    top_defaults = {}
    if root_pom.exists():
      root_mod = self.oracle.parse_pom(root_pom)
      if not root_mod.get("error"):
        if root_mod.get("groupId"):
          top_defaults["groupId"] = root_mod["groupId"]
        if root_mod.get("version"):
          top_defaults["version"] = root_mod["version"]

    modules = []
    errors = []
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
      logger.info("Build: FAIL - POM parsing errors present")
      for pom, err in errors[:5]:
        logger.info(f" - {pom}: {err}")
      if len(errors) > 5:
        logger.info(f" ... {len(errors)-5} more")
      return utils.CheckResult.failure("POM parsing errors present")

    self.oracle._modules = modules
    return utils.CheckResult.success()


@dataclasses.dataclass(frozen=True, slots=True)
class _CodeBuildRequirement(utils.BaseRequirement):
  oracle: "OracleArtifactBuild"

  def check(self, ctx: object) -> utils.CheckResult:
    del ctx

    modules = getattr(self.oracle, "_modules", None)
    if not modules:
      return utils.CheckResult.success()

    missing_targets = []
    missing_installs = []

    for m in modules:
      if not self.oracle.has_target_jar(m):
        missing_targets.append(str(m["dir"]))
      if not self.oracle.has_installed_artifact(m):
        missing_installs.append(f"{m['groupId']}:{m['artifactId']}:{m['version']}")

    if missing_targets or missing_installs:
      logger.info("Code build: FAIL")
      if missing_targets:
        logger.info(" Missing built JARs in target/:")
        for d in missing_targets[:10]:
          logger.info(f"  - {d}")
        if len(missing_targets) > 10:
          logger.info(f"  ... {len(missing_targets)-10} more")
      if missing_installs:
        logger.info(" Missing artifacts in local ~/.m2 repository:")
        for gav in missing_installs[:10]:
          logger.info(f"  - {gav}")
        if len(missing_installs) > 10:
          logger.info(f"  ... {len(missing_installs)-10} more")

      return utils.CheckResult.failure("missing built jars and/or installed artifacts")

    logger.info("Code build: PASS")
    return utils.CheckResult.success()


class OracleArtifactBuild(OracleArtifactBuildBase):
  def __init__(self, *, logger=logger):
    super().__init__(logger=logger)
    self.maven_packages_dir = HOME / ".m2" / "repository"
    self._modules = None

  def requirements(self):
    return (
      _BuildInputsRequirement(name="Build", oracle=self),
      _CodeBuildRequirement(name="Code build", oracle=self),
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

    parent = root.find("parent")
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

  def has_target_jar(self, module):
    if module["packaging"] == "pom":
      return True # no jar expected
    target = module["dir"] / "target"
    if not target.is_dir():
      return False
    pattern = f"{module['artifactId']}-{module['version']}*.jar"
    return any(fnmatch.fnmatch(p.name, pattern) for p in target.glob("*.jar"))

  def has_installed_artifact(self, module):
    rp = self.repo_path(module["groupId"], module["artifactId"], module["version"])
    if module["packaging"] == "pom":
      return (rp / f"{module['artifactId']}-{module['version']}.pom").is_file()
    return any(p.suffix == ".jar" and fnmatch.fnmatch(
          p.name, f"{module['artifactId']}-{module['version']}*.jar")
          for p in rp.glob("*.jar"))