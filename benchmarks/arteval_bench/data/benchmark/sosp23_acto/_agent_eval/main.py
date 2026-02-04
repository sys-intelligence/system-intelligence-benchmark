#!/usr/bin/env python3
"""Runs environment setup checks for ACTO."""

from __future__ import annotations
from pathlib import Path
from typing import Dict
import os
import sys


_AGENT_EVAL_DIR = Path(__file__).resolve().parent
_AGENT_SRC_DIR = _AGENT_EVAL_DIR.parents[3] / "src"
sys.path.append(str(_AGENT_SRC_DIR))


from evaluator.utils import (  # pylint: disable = wrong-import-position
  EntryConfig,
  LoggerConfig,
  get_logger,
  record_result,
)
from oracle_artifact_build import OracleArtifactBuild  # pylint: disable = wrong-import-position
from oracle_env_setup import OracleEnvSetup  # pylint: disable = wrong-import-position


ACTO_CONFIG = EntryConfig(
  name = "sosp23-acto",
  home_dir = Path.home() / "sosp23_acto",
  repository_paths = {"sosp23-acto": (Path.home() / "sosp23_acto" / "acto")},
  results_paths = {
    "table5": (Path.home() / "sosp23_acto" / "acto" / "table5.txt"),
    "table6": (Path.home() / "sosp23_acto" / "acto" / "table6.txt"),
    "table7": (Path.home() / "sosp23_acto" / "acto" / "table7.txt"),
    "table8": (Path.home() / "sosp23_acto" / "acto" / "table8.txt"),
  },
  ground_truth_paths = {
    "table5": (
      Path.home() / "sosp23_acto" / "_agent_eval" / "refs" / "table5.ref.json"
    ),
    "table6": (
      Path.home() / "sosp23_acto" / "_agent_eval" / "refs" / "table6.ref.json"
    ),
    "table7": (
      Path.home() / "sosp23_acto" / "_agent_eval" / "refs" / "table7.ref.json"
    ),
    "table8": (
      Path.home() / "sosp23_acto" / "_agent_eval" / "refs" / "table8.ref.json"
    ),
  },
  similarity_ratio = 0.75,
)


def main(argv: list[str]) -> int:
  verbose = "--verbose" in argv

  results: Dict[str, int] = {}
  score = 0

  logger_name = os.environ.get("EVAL_LOGGER_NAME", "ACTO-EVAL")
  logger = get_logger(LoggerConfig(root_name = logger_name))

  env_checker = OracleEnvSetup(config = ACTO_CONFIG, logger = logger)
  score += record_result(
    logger, results, type(env_checker).__name__, env_checker.run(verbose = verbose)
  )

  build_checker = OracleArtifactBuild(config = ACTO_CONFIG, logger = logger)
  score += record_result(
    logger, results, type(build_checker).__name__, build_checker.run(verbose = verbose)
  )

  logger.info("Agent scores: %s", results)
  return score


if __name__ == "__main__":
  raise SystemExit(main(sys.argv[1:]))