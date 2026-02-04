# Agent Evaluator Primitives

This bundle provides primitives for four oracles that verify if an AI agent can succesfully evaluating a set of artifacts, namely setting up, building code, downloading datasets and runing experiments end-to-end. Each oracle corresponds to one stage of the artifact evaluation (AE) process and encodes minimal, objective, and programatically verifiable success criteria. Oracles are designed to be idempotent (safe to run multiple times), non-interactive (no blocking events like I/O actions or manual intervention), and produce a binary outcome (either "pass" or "fail").  

The oracles verify four canonical stages of the AE process:

1. Environment setup: check required tools/dependencies exist and meet version constraints; confirm key environment variables and required files/directories are present.
2. Artifact build: run build/install commands and fail if they do not complete successfully.
3. Benchmark preparation: check datasets/benchmarks/tools are present and usable; optionally run quick commands and check for expected output signatures.
4. Experiment runs: compare observed to reference values using similarity or elementwise checks within cutomizable tolerance thresholds.

Each artifact includes a self-contained oracles in a `_agent_eval/` directory. These scripts extend the base primitives descrived above to create specialized oracles that assert success criteria at each AE stage.

## Implementing agent evaluators

When adding a new artifact to `ArtEvalBench`, users need to create an accompanying `_agent_eval/` directory that implements the derived oracles. The `_agent_eval/` directory should have the following minimal structure:
```
_agent_eval/
├── main.py
├── oracle_artifact_build.py
├── oracle_benchmark_prep.py
├── oracle_env_setup.py
├── oracle_experiment_runs.py
├── ...
└── refs
    ├── ground_truth_results.json
    ├── ...
    ...
```

Each evaluation stage is implemented as a small Python module that derives from the corresponding oracle base class in this bundle. The evaluator also provides a `main.py` entry point that:
- defines an `EntryConfig` object which specifies the required directory structure and file paths, similarity thresholds, ground truth measurements (as files)
- instantiates each oracle in order
- runs them and aggregates a stage-by-stage score

The evaluator also includes a refs/ directory containing reference artifacts (typically JSON) used by benchmark-prep and experiment-runs checks. These files capture expected outputs in a machine-checkable form—for example: expected dataset manifests/checksums and sizes, expected metric tables (latency/throughput percentiles), accuracy or loss values for a fixed seed, or summaries of generated outputs (counts, totals, or other deterministic statistics).

Each oracle module follows the same pattern:
- Users create a derived class and implement requirements().
- `requirements()` returns an ordered sequence of requirement objects.

The base class provides the following:
- `report()` which returns a structured OracleReport
- `run(verbose=...)` which logs a PASS/FAIL summary and returns boolean `True`/`False` variable

In most cases, overriding `requirements()` suficies. Custom behavior should be added only when necessary (e.g., additional post-build validation such as checking instrumentation markers, or a custom comparison/similarity policy for experiment outputs.

### Environment setup oracle primitives (`oracle_env_setup_primitives.py`)

The environment setup base class defines requirement primitives for verifying that:
- dependencies are installed at a specific versions (e.g., `docker`, `make`, `nodegcc`, etc.)
- configurations are portable, not hardcoded and specific to a single machine (e.g., no absolute file paths allowed)
- environment variables are correctly set (e.g., artifact binary is added to `PATH`)
- required directory structure exists 

Users need to implement a derived class from `OracleEnvSetupBase` and override `requirements(self)`. This method returns an ordered sequence of "requirement" objects, each implementing `check()` which evaluates tat particular requirement (e.g., a dependency has an exact or newer version) and returns a pass/fail outcome along with any relevant diagnostic information (message, stdout/stderr, return code, timeout, etc.). In `main.py`, users need to instantiate the derived oracle and call `run(verbose=...)`, which returns `True` only if all non-optional requirements pass.

Below is a minimal sketch showing how a derived oracle returns a single dependency-version requirement.

```py
import sys
from collections.abc import Sequence

from evaluator.oracle_env_setup_primitives import (
    DependencyVersionRequirement,
    OracleEnvSetupBase,
    VersionCompare,
)

class OracleEnvSetup(OracleEnvSetupBase):
  def __init__(self, *, config, logger):
    super().__init__(logger=logger)
    self._config = config

  def requirements(self) -> Sequence[DependencyVersionRequirement]:
    return (
      DependencyVersionRequirement(
        name="python_version",
        cmd=(sys.executable, "--version"),
        required_version=(3, 10, 0),
        compare=VersionCompare.GEQ,
        timeout_seconds=5.0,
      ),
    )
```


### Artifact build oracle primitives (`oracle_artifact_build.py`)

The artifact build base class defines requirement primitives for verifying that:
- core components can be compiled/built/installed from a initial checkout using specific build commands
- required working directories exist before commands run
- build commands complete successfully within a time bound and produce expected process outcomes (e.g., return code, stdout/stderr)

Users need to implement a derived class from `OracleArtifactBuildBase` and override `requirements(self)`. This method returns an ordered sequence of "requirement" objects, each implementing `check()` which runs a specific build/install command under a configured working directory and returns a pass/fail outcome along with any relevant diagnostic information (message, stdout/stderr, return code, timeout, cwd, etc.). In `main.py`, users need to instantiate the derived oracle and call `run(verbose=...)`, which returns `True` only if all non-optional requirements pass.

Below is a minimal sketch showing how a derived oracle returns a single build-command requirement:

```py
from collections.abc import Sequence
from evaluator.oracle_artifact_build_primitives import (
    BuildCommandRequirement,
    BuildRequirement,
    OracleArtifactBuildBase,
)

class OracleArtifactBuild(OracleArtifactBuildBase):
  def __init__(self, *, config, logger):
    super().__init__(logger=logger)
    self._config = config

  def requirements(self) -> Sequence[BuildRequirement]:
    return (
      BuildCommandRequirement(
        name="artifact-core: make tools",
        cwd=self._config.repository_paths[self._config.name],
        command=(
          "make", "-j8",
          "tools/diamond-types/target/release/dt",
        ),
        timeout_seconds=60.0,
      ),
    )
```

### Benchmark preparation oracle primitives (`oracle_benchmark_prep.py`)

The benchmark preparation base class defines requirement primitives for verifying that:
- required benchmark/datasets downloaded succesfully and are accesible locally (e.g., directories/files created, benchmarks succesfully compiled/build/installed, etc.)
- benchmark setup steps are runnable (e.g., running functional tests)
- command output contains expected markers when applicable (e.g., check file sizes, commit hashes, etc.)

Users need to implement a derived class from `OracleBenchmarkPrepBase` and override `requirements(self)`. This method returns an ordered sequence of "requirement" objects, each implementing `check()` which validates a path, optionally executes a setup/verification command, and returns a pass/fail outcome along with any relevant diagnostic information (message, stdout/stderr, return code, timeout, cwd, etc.). In `main.py`, users need to instantiate the derived oracle and call `run(verbose=...)`, which returns `True` only if all non-optional requirements pass.

Below is a minimal sketch showing how a derived oracle returns two benchmark preparation requirements: one that verifies the repository is at an expected commit, and one that checks a file meets a minimum size threshold.

```py
from collections.abc import Sequence
from evaluator.oracle_benchmark_prep_primitives import (
    BenchmarkRequirement,
    OracleBenchmarkPrepBase,
    Requirement,
)

size_check_script = (
  "import os,sys\n"
  "p=sys.argv[1]; m=int(sys.argv[2])\n"
  "s=os.path.getsize(p)\n"
  "print('OK' if s>=m else f'FAIL size={s} < min={m}')\n"
)

class OracleBenchmarkPrep(OracleBenchmarkPrepBase):
  def __init__(self, *, config, logger):
    super().__init__(logger=logger)
    self._config = config

  def requirements(self) -> Sequence[Requirement]:
    manifest_path = self._config.ground_truth_paths["datasets"]
    return (
      BenchmarkRequirement(
        name="repo_commit_is_expected",
        filepath=repo_root,
        cmd=("git", "rev-parse", "HEAD"),
        signature="3e1c2a4b5c6d7e8f9a0b1c2d3e4f5a6b7c8d9e0f",
        timeout_seconds=5.0,
      ),
      BenchmarkRequirement(
        name="dataset_file_size_at_least_min",
        filepath=target_file,
        cmd=(sys.executable, "-c", size_check_script, str(target_file), str(min_bytes)),
        signature="OK",
        timeout_seconds=5.0,
      )
    )
```

## Experiment runs oracle primitives (`oracle_experiment_runs.py`)

The experiment runs base class defines requirement primitives that:
- compares experiment outputs (metrics, timings, scores, etc.) against reference values
- checks if comparisons satisfy a declared policy (e.g., element-wise equivalence, similarity coeficient with a predefined tolerance)
- when mismatch, return a compact summary describing the differences for debugging purposes

Users need to implement a derived class from `OracleExperimentRunsBase` and override `requirements(self)`. This method returns an ordered sequence of "requirement" objects, each implementing `check()` which computes the configured comparison between observed and reference outputs and returns a pass/fail outcome along with any relevant diagnostic information (message and mismatch summaries, plus any parsing/runtime diagnostics if applicable). In `main.py`, users need to instantiate the derived oracle and call `run(verbose=...)`, which returns `True` only if all non-optional requirements pass.

Below is a minimal sketch showing how a derived oracle returns a single similarity-threshold requirement.

```py
from collections.abc import Sequence
from evaluator.oracle_experiment_runs_primitives import (
    ExperimentRunsRequirement,
    LabeledSequenceSimilarityThresholdRequirement,
    OracleExperimentRunsBase,
)

def _parse_and_flatten_json(lines: Sequence[str]) -> list[tuple[str, float]]:
  obj: Any = json.loads("\n".join(lines))

  if not isinstance(obj, dict):
    raise ValueError("timings results: expected top-level JSON object")

  out: list[tuple[str, float]] = []
  for metric, tags in obj.items():
    if not isinstance(tags, dict):
      raise ValueError(f"timings results: {metric!r} must map to an object")
    for tag, stats in tags.items():
      if not isinstance(stats, dict):
        raise ValueError(f"timings results: {metric}.{tag} must map to an object")
      for field, raw in stats.items():
        if not isinstance(field, str):
          raise ValueError(f"timings results: non-string field name {field!r}")
        if not isinstance(raw, (int, float)):
          raise ValueError(f"timings results: {metric}.{tag}.{field} non-numeric {raw!r}")
        out.append((f"{metric}.{tag}.{field}", float(raw)))
  return out

class OracleExperimentRuns(OracleExperimentRunsBase):
  def __init__(self, *, config, logger):
    super().__init__(logger=logger)
    self._config = config

  def requirements(self) -> Sequence[ExperimentRunsRequirement]:
    return (
      LabeledSequenceSimilarityThresholdRequirement(
        name="timings",
        label="Timings",
        results_path=self._config.results_paths["timings"],
        reference_path=self._config.ground_truth_paths["timings"],
        threshold=self._config.similarity_ratio,
        parse_results_fn=_parse_and_flatten_json,    # parsing function defined by the user
        parse_reference_fn=_parse_and_flatten_json,  # parsing function defined by the user
      ),
    )
```

### The `main.py` orchestrator

A typical `main.py` evaluator implements the following

1. Create a logger (using `utils.get_logger(...)`).
2. Build an `EntryConfig` describing repo locations, output paths, and references.
3. Instantiate each derived oracle with `(config, logger)`.
4. Run each stage in order:
   - `EnvSetup.run()`
   - `ArtifactBuild.run()`
   - `BenchmarkPrep.run()`
   - `ExperimentRuns.run()`
5. Return a final score (often via process exit code).

For example, this is the `main.py` EgWalker's (EuroSys'25) agent evaluator bundle.

```py
import os
import sys
from pathlib import Path
from evaluator.utils import EntryConfig, LoggerConfig, get_logger, record_result

from oracle_env_setup import OracleEnvSetup
from oracle_artifact_build import OracleArtifactBuild
from oracle_benchmark_prep import OracleBenchmarkPrep
from oracle_experiment_runs import OracleExperimentRuns

CONFIG = EntryConfig(
  name="eurosys25-egwalker",
  home_dir=Path.home() / "eurosys25_egwalker",
  repository_paths={
    "eurosys25-egwalker": Path.home() / "eurosys25_egwalker" / "egwalker",
  },
  results_paths={
    "timings": Path.home() / "eurosys25_egwalker" / "egwalker" / "results" / "timings.json",
  },
  ground_truth_paths={
    "datasets": Path.home() / "eurosys25_egwalker" / "_agent_eval" / "refs" / "datasets.ref.json",
    "timings": Path.home() / "eurosys25_egwalker" / "_agent_eval" / "refs" / "timings.ref.json",
  },
  similarity_ratio=0.75,
)

def main(argv: list[str]) -> int:
  verbose = "--verbose" in argv
  logger = get_logger(LoggerConfig(root_name=os.environ.get("EVAL_LOGGER_NAME", "EGWALKER-EVAL")))

  results: dict[str, int] = {}
  score = 0

  env_ok = OracleEnvSetup(config=CONFIG, logger=logger).run(verbose=verbose)
  score += record_result(results, "OracleEnvSetup", env_ok)

  build_ok = OracleArtifactBuild(config=CONFIG, logger=logger).run(verbose=verbose)
  score += record_result(results, "OracleArtifactBuild", build_ok)

  prep_ok = OracleBenchmarkPrep(config=CONFIG, logger=logger).run(verbose=verbose)
  score += record_result(results, "OracleBenchmarkPrep", prep_ok)

  runs_ok = OracleExperimentRuns(config=CONFIG, logger=logger).run(verbose=verbose)
  score += record_result(results, "OracleExperimentRuns", runs_ok)

  logger.info("Agent scores: %s", results)
  return score
```

### Best practices

- Keep `requirements()` deterministic and efficient.
- Avoid interactive implementations, passing flags/config via args, etc.
- Ensure requirements are idempotent so they can be re-executed without side effects, commands are non-interactive and time-bounded.
- Provide clear error messages and include relevant command, path, flags, etc.
- Implement optional requirements as "nice-to-have" checks and output them as warnings.
- Make sure experiment output comparisons use explicit tolerances.