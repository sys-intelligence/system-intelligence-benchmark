#!/usr/bin/env python3
"""Runs environment setup, build, benchmark prep, and experiment runs checks for EGWALKER."""

from __future__ import annotations

import os
import sys
from pathlib import Path
from typing import Dict

_AGENT_EVAL_DIR = Path(__file__).resolve().parent
_AGENT_SRC_DIR = _AGENT_EVAL_DIR.parents[3] / "src"
sys.path.append(str(_AGENT_SRC_DIR))

from oracle_artifact_build import OracleArtifactBuild
from oracle_benchmark_prep import OracleBenchmarkPrep
from oracle_env_setup import OracleEnvSetup
from oracle_experiment_runs import OracleExperimentRuns
from evaluator.utils import EntryConfig, LoggerConfig, get_logger, record_result


EGWALKER_CONFIG = EntryConfig(
    name="eurosys25-egwalker",
    home_dir=Path.home() / "eurosys25_egwalker",
    repository_paths={
        "eurosys25-egwalker": Path.home() / "eurosys25_egwalker" / "egwalker",
    },
    results_paths={
        # Matches legacy: <repo>/results/timings.json
        "timings": Path.home()
        / "eurosys25_egwalker"
        / "egwalker"
        / "results"
        / "timings.json",
    },
    ground_truth_paths={
        "datasets": (
            Path.home()
            / "eurosys25_egwalker"
            / "_agent_eval"
            / "refs"
            / "datasets.ref.json"
        ),
        "timings": (
            Path.home()
            / "eurosys25_egwalker"
            / "_agent_eval"
            / "refs"
            / "timings.ref.json"
        ),
    },
    similarity_ratio=0.75,
)


def main(argv: list[str]) -> int:
  results: Dict[str, int] = {}
  score = 0

  verbose = "--verbose" in argv

  logger_name = os.environ.get("EVAL_LOGGER_NAME", "EGWALKER-EVAL")
  logger = get_logger(LoggerConfig(root_name=logger_name))

  env_checker = OracleEnvSetup(config=EGWALKER_CONFIG, logger=logger)
  score += record_result(
      logger, results, type(env_checker).__name__, env_checker.run(verbose=verbose)
  )

  build_checker = OracleArtifactBuild(config=EGWALKER_CONFIG, logger=logger)
  score += record_result(
      logger, results, type(build_checker).__name__, build_checker.run(verbose=verbose)
  )

  prep_checker = OracleBenchmarkPrep(config=EGWALKER_CONFIG, logger=logger)
  score += record_result(
      logger, results, type(prep_checker).__name__, prep_checker.run(verbose=verbose)
  )

  runs_checker = OracleExperimentRuns(config=EGWALKER_CONFIG, logger=logger)
  score += record_result(
      logger, results, type(runs_checker).__name__, runs_checker.run(verbose=verbose)
  )

  logger.info("Agent scores: %s", results)
  return score


if __name__ == "__main__":
  raise SystemExit(main(sys.argv[1:]))
