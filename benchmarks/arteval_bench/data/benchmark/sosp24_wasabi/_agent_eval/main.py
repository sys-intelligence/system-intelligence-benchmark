#!/usr/bin/env python3
"""Runs environment setup checks for WASABI."""

from __future__ import annotations

from pathlib import Path
from typing import Dict
import os
import sys



from evaluator.utils import (
    EntryConfig,
    LoggerConfig,
    get_logger,
    record_result,
)
from oracle_artifact_build import OracleArtifactBuild
from oracle_env_setup import OracleEnvSetup
from oracle_benchmark_prep import OracleBenchmarkPrep
from oracle_experiment_runs import OracleExperimentRuns


_AGENT_EVAL_DIR = Path(__file__).resolve().parent
_WASABI_HOME = _AGENT_EVAL_DIR.parent.resolve()
_WASABI_REPO = (_WASABI_HOME / "wasabi" / "wasabi-testing").resolve()
_WASABI_BENCH = (_WASABI_HOME / "benchmarks").resolve()


WASABI_CONFIG = EntryConfig(
  name="sosp24-wasabi",
  home_dir=_WASABI_HOME,
  repository_paths={
      "sosp24-wasabi": _WASABI_REPO,
      "benchmarks": _WASABI_BENCH,
  },
  results_paths={
      "results_root": _WASABI_REPO / "results",
  },
  ground_truth_paths={
      "bugs_ground_truth": _AGENT_EVAL_DIR / "refs" / "bugs_ground_truth.csv",
  },
  similarity_ratio=0.75,
  metadata={
      "maven_repo_dir": Path.home() / ".m2" / "repository",

      "weaving_plugin_signature": "aspectj-maven-plugin",

      "primary_artifact": "edu.uchicago.cs.systems:wasabi",

      "benchmarks": {
          "hadoop": {
              "repo_url": "https://github.com/apache/hadoop.git",
              "commit": "60867de",
              "pom_file": "pom.xml",
              "pom_backup": "pom-original.xml",
          },
          "hbase": {
              "repo_url": "https://github.com/apache/hbase.git",
              "commit": "89ca7f4",
              "pom_file": "pom.xml",
              "pom_backup": "pom-original.xml",
          },
          "hive": {
              "repo_url": "https://github.com/apache/hive.git",
              "commit": "e08a600",
              "pom_file": "pom.xml",
              "pom_backup": "pom-original.xml",
          },
      },

      "aspectj_markers": [
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
      ],
  },
)


def main(argv: list[str]) -> int:
  verbose = "--verbose" in argv

  results: Dict[str, int] = {}
  score = 0

  logger_name = os.environ.get("EVAL_LOGGER_NAME", "WASABI-AGENT-EVALUATOR")
  logger = get_logger(LoggerConfig(root_name=logger_name))

  env_checker = OracleEnvSetup(config=WASABI_CONFIG, logger=logger)
  env_ok = env_checker.run(verbose=verbose)
  score += record_result(results, type(env_checker).__name__, env_ok)

  build_checker = OracleArtifactBuild(config=WASABI_CONFIG, logger=logger)
  build_ok = build_checker.run(verbose=verbose)
  score += record_result(results, type(build_checker).__name__, build_ok)

  prep_checker = OracleBenchmarkPrep(config=WASABI_CONFIG, logger=logger)
  prep_ok = prep_checker.run(verbose=verbose)
  score += record_result(results, type(prep_checker).__name__, prep_ok)

  runs_checker = OracleExperimentRuns(config=WASABI_CONFIG, logger=logger)
  runs_ok = runs_checker.run(verbose=verbose)
  score += record_result(results, type(runs_checker).__name__, runs_ok)

  logger.info("Agent scores: %s", results)
  return score


if __name__ == "__main__":
  raise SystemExit(main(sys.argv[1:]))
