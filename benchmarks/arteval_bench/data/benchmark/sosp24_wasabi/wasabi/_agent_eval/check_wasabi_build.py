#!/usr/bin/env python3
import sys
import os
from pathlib import Path
import xml.etree.ElementTree as ET
import fnmatch

BASE = Path.home() / "sosp24-ae" / "wasabi" / "wasabi-testing"
M2 = Path.home() / ".m2" / "repository"

# XML namespace-safe helper
def xget(elem, tag):
    # Handle tags with or without default namespace
    if elem is None:
        return None
    # Try direct
    v = elem.find(tag)
    if v is not None and v.text:
        return v.text.strip()
    # Try any namespace
    for child in elem:
        t = child.tag.split('}', 1)[-1]  # strip "{ns}"
        if t == tag:
            return (child.text or "").strip()
    return None

def parse_pom(pom_path, top_defaults=None):
    """
    Returns dict with keys: dir, pom, groupId, artifactId, version, packaging
    Inherits groupId/version from parent or provided top_defaults.
    """
    try:
        tree = ET.parse(pom_path)
        root = tree.getroot()
    except Exception as e:
        return {"dir": pom_path.parent, "pom": pom_path, "error": f"XML parse error: {e}"}

    # Maven POM default packaging is "jar"
    artifactId = xget(root, "artifactId")
    groupId = xget(root, "groupId")
    version = xget(root, "version")
    packaging = xget(root, "packaging") or "jar"

    parent = root.find("parent")
    if parent is not None:
        p_groupId = xget(parent, "groupId")
        p_version = xget(parent, "version")
        # artifactId of parent is irrelevant for inheritance here
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

def find_poms(base):
    return sorted(base.rglob("pom.xml"))

def repo_path(groupId, artifactId, version):
    parts = groupId.split(".")
    return M2.joinpath(*parts, artifactId, version)

def has_target_jar(module):
    if module["packaging"] == "pom":
        return True  # no jar expected
    target = module["dir"] / "target"
    if not target.is_dir():
        return False
    # look for artifactId-version*.jar (allow classifiers, shaded, etc.)
    pattern = f"{module['artifactId']}-{module['version']}*.jar"
    return any(fnmatch.fnmatch(p.name, pattern) for p in target.glob("*.jar"))

def has_installed_artifact(module):
    rp = repo_path(module["groupId"], module["artifactId"], module["version"])
    if module["packaging"] == "pom":
        return (rp / f"{module['artifactId']}-{module['version']}.pom").is_file()
    # prefer exact jar; allow classifiers
    return any(p.suffix == ".jar" and fnmatch.fnmatch(
               p.name, f"{module['artifactId']}-{module['version']}*.jar")
               for p in rp.glob("*.jar"))

def main():
    # Basic presence
    if not BASE.exists():
        print("Build: FAIL - base project directory not found")
        sys.exit(1)

    poms = find_poms(BASE)
    if not poms:
        print("Build: FAIL - no pom.xml files found under wasabi-testing")
        sys.exit(1)

    # Establish top-level defaults (groupId/version) from the root POM (closest to BASE)
    root_pom = BASE / "pom.xml"
    top_defaults = {}
    if root_pom.exists():
        root_mod = parse_pom(root_pom)
        if not root_mod.get("error"):
            if root_mod.get("groupId"):
                top_defaults["groupId"] = root_mod["groupId"]
            if root_mod.get("version"):
                top_defaults["version"] = root_mod["version"]

    modules = []
    errors = []
    for pom in poms:
        m = parse_pom(pom, top_defaults=top_defaults)
        if m.get("error"):
            errors.append((pom, m["error"]))
            continue
        # Sanity: must have these
        if not all([m.get("artifactId"), m.get("groupId"), m.get("version")]):
            errors.append((pom, "missing groupId/artifactId/version after inheritance"))
        else:
            modules.append(m)

    if errors:
        # Parsing problems → cannot reliably assert build
        print("Build: FAIL - POM parsing errors present")
        for pom, err in errors[:5]:
            print(f"  - {pom}: {err}")
        if len(errors) > 5:
            print(f"  ... {len(errors)-5} more")
        sys.exit(1)

    # Evaluate modules
    missing_targets = []
    missing_installs = []

    for m in modules:
        # skip aggregator-only modules that are 'pom' packaging for target check
        if not has_target_jar(m):
            missing_targets.append(str(m["dir"]))
        if not has_installed_artifact(m):
            missing_installs.append(f"{m['groupId']}:{m['artifactId']}:{m['version']}")

    # Decide overall result
    if missing_targets or missing_installs:
        print("Build: FAIL")
        if missing_targets:
            print("  Missing built JARs in target/:")
            for d in missing_targets[:10]:
                print(f"    - {d}")
            if len(missing_targets) > 10:
                print(f"    ... {len(missing_targets)-10} more")
        if missing_installs:
            print("  Missing artifacts in local ~/.m2 repository:")
            for gav in missing_installs[:10]:
                print(f"    - {gav}")
            if len(missing_installs) > 10:
                print(f"    ... {len(missing_installs)-10} more")
        sys.exit(1)
    else:
        print("Build: PASS")
        sys.exit(0)

if __name__ == "__main__":
    main()
