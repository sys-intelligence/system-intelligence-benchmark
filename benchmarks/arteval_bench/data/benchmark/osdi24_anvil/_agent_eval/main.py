#!/usr/bin/env python3
"""Runs environment setup checks for ANVIL."""

from __future__ import annotations

import os
import sys
from pathlib import Path
from typing import Dict

_AGENT_EVAL_DIR = Path(__file__).resolve().parent
_AGENT_SRC_DIR = _AGENT_EVAL_DIR.parents[3] / "src"
sys.path.append(str(_AGENT_SRC_DIR))

from oracle_env_setup import OracleEnvSetup
from oracle_artifact_build import OracleArtifactBuild
from oracle_benchmark_prep import OracleBenchmarkPrep
from oracle_experiment_runs import OracleExperimentRuns
from evaluator.utils import (
    EntryConfig,
    LoggerConfig,
    get_logger,
    record_result,
)

# Reuse the same constants the legacy oracle used.
from utils import RESULTS_PATH, SIMILARITY_RATIO  # pylint: disable=wrong-import-position


ANVIL_CONFIG = EntryConfig(
    name="osdi24-anvil",
    home_dir=Path.home() / "osdi24_anvil",
    repository_paths={
        "osdi24-anvil": Path.home() / "osdi24_anvil" / "anvil",
        "osdi24-acto-dependency": Path.home() / "osdi24_anvil" / "acto",
    },
    results_paths={
        "table3": Path(RESULTS_PATH),
    },
    ground_truth_paths={
        "table3": (
            Path.home()
            / "osdi24_anvil"
            / "_agent_eval"
            / "refs"
            / "anvil-table-3.ref.json"
        ),
    },
    similarity_ratio=SIMILARITY_RATIO,
)


def main(argv: list[str]) -> int:
  results: Dict[str, int] = {}
  score = 0

  verbose = "--verbose" in argv

  logger_name = os.environ.get("EVAL_LOGGER_NAME", "ANVIL-EVAL")
  logger = get_logger(LoggerConfig(root_name=logger_name))

  env_checker = OracleEnvSetup(config=ANVIL_CONFIG, logger=logger)
  score += record_result(
      results, type(env_checker).__name__, env_checker.run(verbose=verbose)
  )

  build_checker = OracleArtifactBuild(config=ANVIL_CONFIG, logger=logger)
  score += record_result(
      results, type(build_checker).__name__, build_checker.run(verbose=verbose)
  )

  prep_checker = OracleBenchmarkPrep(config=ANVIL_CONFIG, logger=logger)
  score += record_result(
      results, type(prep_checker).__name__, prep_checker.run(verbose=verbose)
  )

  runs_checker = OracleExperimentRuns(config=ANVIL_CONFIG, logger=logger)
  score += record_result(
      results, type(runs_checker).__name__, runs_checker.run(verbose=verbose)
  )

  logger.info("Agent scores: %s", results)
  return score


if __name__ == "__main__":
  raise SystemExit(main(sys.argv[1:]))
