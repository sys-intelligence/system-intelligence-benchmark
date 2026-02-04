#!/usr/bin/env python3
"""Runs environment setup checks for WASABI."""

from __future__ import annotations
from pathlib import Path
from typing import Dict
import os
import sys


_AGENT_EVAL_DIR = Path(__file__).resolve().parent
_AGENT_SRC_DIR = _AGENT_EVAL_DIR.parents[3] / "src"
sys.path.append(str(_AGENT_SRC_DIR))


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


# NOTE: WASABI bundle layout mirrors the legacy constants, but we build it directly
# from EntryConfig rather than importing legacy globals.
_WASABI_HOME = Path.home() / "sosp24_wasabi"
_WASABI_REPO = _WASABI_HOME / "wasabi"
_WASABI_BENCH = _WASABI_HOME / "benchmarks"


WASABI_CONFIG = EntryConfig(
  name = "sosp24-wasabi",
  home_dir = _WASABI_HOME,
  repository_paths = {
    "sosp24-wasabi": _WASABI_REPO,
    "benchmarks": _WASABI_BENCH,
  },
  results_paths = {
    "results_root": _WASABI_REPO / "results",
  },
  ground_truth_paths = {
    "bugs_ground_truth": _WASABI_REPO / "bugs_ground_truth.txt",
  },
  similarity_ratio = 0.75,
)


def main(argv: list[str]) -> int:
  verbose = "--verbose" in argv

  results: Dict[str, int] = {}
  score = 0

  logger_name = os.environ.get("EVAL_LOGGER_NAME", "WASABI-AGENT-EVALUATOR")
  logger = get_logger(LoggerConfig(root_name = logger_name))

  env_checker = OracleEnvSetup(config = WASABI_CONFIG, logger = logger)
  score += record_result(
    logger, results, type(env_checker).__name__, env_checker.run(verbose = verbose)
  )

  build_checker = OracleArtifactBuild(config = WASABI_CONFIG, logger = logger)
  score += record_result(
    logger, results, type(build_checker).__name__, build_checker.run(verbose = verbose)
  )

  prep_checker = OracleBenchmarkPrep(config = WASABI_CONFIG, logger = logger)
  score += record_result(
    logger, results, type(prep_checker).__name__, prep_checker.run(verbose = verbose)
  )

  runs_checker = OracleExperimentRuns(config = WASABI_CONFIG, logger = logger)
  score += record_result(
    logger, results, type(runs_checker).__name__, runs_checker.run(verbose = verbose)
  )

  logger.info("Agent scores: %s", results)
  return score


if __name__ == "__main__":
  raise SystemExit(main(sys.argv[1:]))
