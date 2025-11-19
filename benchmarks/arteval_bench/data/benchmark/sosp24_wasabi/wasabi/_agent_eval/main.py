#!/usr/bin/env python3
import sys
from typing import Dict

from oracle_artifact_build import OracleArtifactBuild
from oracle_env_setup import OracleEnvSetup
from oracle_benchmark_prep import OracleBenchmarkPrep
from oracle_experiment_runs import OracleExperimentRuns

from utils import logger

def main():
  results: Dict[str, int] = {}

  for cls in (OracleEnvSetup, OracleArtifactBuild, OracleBenchmarkPrep, OracleExperimentRuns):
    checker = cls()
    ok = checker.run()
    name = cls.__name__
    logger.info(f"{name}: {'PASS' if ok else 'FAIL'}")
    results[name] = 1 if ok else 0

  logger.info(f"Agent scores: {results}")
  return results


if __name__ == "__main__":
  main()