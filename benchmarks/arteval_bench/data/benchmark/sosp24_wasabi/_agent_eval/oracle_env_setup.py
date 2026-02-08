#!/usr/bin/env python3
"""Environment setup oracle for WASABI.

This oracle reuses the shared env-setup primitives to validate:
  * Toolchain dependencies and versions referenced by the WASABI README.
  * Environment variables WASABI_ROOT_DIR and JAVA_HOME (exact string match).
  * Updated directory structure for the flattened WASABI repo layout.
"""

from __future__ import annotations

import logging
from pathlib import Path
from typing import Sequence

from evaluator import utils
from evaluator.oracle_env_setup_primitives import (
    DependencyVersionRequirement,
    EnvironmentVariableRequirement,
    FilesystemPathRequirement,
    OracleEnvSetupBase,
    PathType,
    VersionCompare,
)

class OracleEnvSetup(OracleEnvSetupBase):
  """WASABI environment setup oracle."""

  _JAVA_HOME = "/usr/lib/jvm/java-8-openjdk-amd64/jre" # Check for Java 1.8

  def __init__(self, *, config: utils.EntryConfig, logger=logging.Logger) -> None:
    super().__init__(logger=logger)
    self._config = config
    self._wasabi_root = Path(self._config.repository_paths[self._config.name]).resolve()
    self._benchmarks_root = Path(self._config.repository_paths["benchmarks"]).resolve()

  def requirements(self) -> Sequence[utils.BaseRequirement]:
    wasabi_root_str = str(self._wasabi_root)

    return (
        # Dependencies, toolchains, and third-party utilites
        DependencyVersionRequirement(
            name="git",
            cmd=("git", "--version"),
            required_version=(0, 0, 0),
            compare=VersionCompare.GEQ,
            timeout_seconds=5.0,
        ),
        DependencyVersionRequirement(
            name="maven",
            cmd=("mvn", "-v"),
            required_version=(3, 6, 3),
            compare=VersionCompare.GEQ,
            version_regex=r"Apache Maven\s+([0-9.]+)",
            timeout_seconds=5.0,
        ),
        DependencyVersionRequirement(
            name="gradle",
            cmd=("gradle", "-v"),
            required_version=(4, 4, 1),
            compare=VersionCompare.GEQ,
            version_regex=r"Gradle\s+([0-9.]+)",
            timeout_seconds=5.0,
        ),
        DependencyVersionRequirement(
            name="ant",
            cmd=("ant", "-version"),
            required_version=(1, 10, 0),
            compare=VersionCompare.GEQ,
            version_regex=r"version\s+([0-9.]+)",
            timeout_seconds=5.0,
        ),
        DependencyVersionRequirement(
            name="python3",
            cmd=("python3", "--version"),
            required_version=(3, 10, 0),
            compare=VersionCompare.GEQ,
            version_regex=r"Python\s+([0-9.]+)",
            timeout_seconds=5.0,
        ),
        DependencyVersionRequirement(
            name="java",
            cmd=("java", "-version"),
            required_version=(1, 8, 0),
            compare=VersionCompare.EQ,
            version_regex=r'version\s+"([^"]+)"',
            timeout_seconds=5.0,
        ),
        DependencyVersionRequirement(
            name="tree",
            cmd=("tree", "--version"),
            required_version=(0, 0, 0),
            compare=VersionCompare.GEQ,
            optional=True,
            timeout_seconds=5.0,
        ),

        # Environment variables
        EnvironmentVariableRequirement(
            name="WASABI_ROOT_DIR matches expected",
            env_var="WASABI_ROOT_DIR",
            expected=str(self._wasabi_root.resolve().parent),
        ),
        FilesystemPathRequirement(
            name="WASABI root directory exists",
            path=self._wasabi_root,
            path_type=PathType.DIRECTORY,
        ),
        EnvironmentVariableRequirement(
            name="JAVA_HOME matches expected",
            env_var="JAVA_HOME",
            expected=self._JAVA_HOME,
        ),
        FilesystemPathRequirement(
            name="JAVA_HOME directory exists",
            path=Path(self._JAVA_HOME),
            path_type=PathType.DIRECTORY,
        ),

        # Directory structure and required exported configs
        FilesystemPathRequirement(
            name="benchmarks directory exists",
            path=self._benchmarks_root,
            path_type=PathType.DIRECTORY,
        ),
        FilesystemPathRequirement(
            name="config directory exists",
            path=self._wasabi_root / "config",
            path_type=PathType.DIRECTORY,
        ),
        FilesystemPathRequirement(
            name="utils directory exists",
            path=self._wasabi_root / "utils",
            path_type=PathType.DIRECTORY,
        ),
        FilesystemPathRequirement(
            name="pom.xml exists",
            path=self._wasabi_root / "pom.xml",
            path_type=PathType.FILE,
        ),

        # Required build/running scripts
        FilesystemPathRequirement(
            name="utils/prereqs.sh exists",
            path=self._wasabi_root / "utils" / "prereqs.sh",
            path_type=PathType.FILE,
        ),
        FilesystemPathRequirement(
            name="utils/run.py exists",
            path=self._wasabi_root / "utils" / "run.py",
            path_type=PathType.FILE,
        ),
        FilesystemPathRequirement(
            name="utils/display_bug_results.py exists",
            path=self._wasabi_root / "utils" / "display_bug_results.py",
            path_type=PathType.FILE,
        ),

        # Required configuration files
        FilesystemPathRequirement(
            name="config/hadoop/example.conf exists",
            path=self._wasabi_root / "config" / "hadoop" / "example.conf",
            path_type=PathType.FILE,
        ),
        FilesystemPathRequirement(
            name="config/hadoop/hadoop.conf exists",
            path=self._wasabi_root / "config" / "hadoop" / "hadoop.conf",
            path_type=PathType.FILE,
        ),
        FilesystemPathRequirement(
            name="config/hadoop/pom-hadoop.xml exists",
            path=self._wasabi_root / "config" / "hadoop" / "pom-hadoop.xml",
            path_type=PathType.FILE,
        ),
    )