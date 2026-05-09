# ArtEvalBench (Archived)

> [!IMPORTANT]  
> This benchmark is archived. We are refactoring it and the new one (AEBench) will be avaiavle at [https://github.com/sys-intelligence/aebench-dev](https://github.com/sys-intelligence/aebench-dev). 

`ArtEvalBench` is a benchmark for evaluating AI agents against Artifact Evaluation (AE) tasks ([why artifact evaluation?](WHY.md)). We believe that, despite the complexity of the AE process, AI agents can be succesfully trained to automatically evaluate artifacts that accompany research papers.

## Contributor's guide

#### » Overview and high-level structure

To train and improve AE agents in a principled way, we introduce `ArtEvalBench`, a curated collection of artifacts accompanying peer-reviewed papers. To ensure a fair comparison, we include artifacts that have already been evaluated in an official AE process and awarded all three badges by the committee. Each entry includes the original artifact (instructions, code, scripts, datasets/benchmarks, etc.), the original paper, and a collection of "oracle" scripts that define objective checkpoints at four canonical stages: environment setup, build/install, benchmark preparation, and experiment execution.

`ArtEvalBench` is designed to evaluate agents on capability (which stages they complete), efficiency (wall-clock time and intervention count), and fidelity (how closely reproduced results match those reported).

To check those capabilities, each artifact includes four oracle scripts that encode minimal, verifiable success criteria for each of the four stages. The oracles are invoked non-interactively and must be idempotent. Conceptually, these four stages correspond to:

1. **Environment setup.** verifies presence and versions of required tools, libraries, or other dependencies; confirms hardware availability when applicable; and checks that configurations are portable rather than hardcoded or tied to a specific machine.
2. **Build (and install) the artifact.** confirms a complete build (or install) operation from a specified version, with expected binaries/modules present; running tests, when available, or simple validation commands like invoking `--help` or equivalent.
3. **Benchmark preparation.** asserts that datasets/benchmarks are present and checksums match; verifies that necessary third-party tools compile and the artifact's instrumentation/monitoring hooks are enabled, if applicable.
4. **Experiment runs.** executes each experiment according to the authors' guidelines; checks that the artifact produces the expected metrics, logs, files, figures, etc.; provides an initial assessment relative to specified tolerance bounds.

#### » Adding a new artifact

Adding to the benchmark requires users to include a new entry into `ArtEvalBench` [schema file](data/benchmark/arteval_tasks.jsonl), where:
- `artifact_id` is a unique identifier for the artifact;
- `artifact_dir` the artifact directory within `data/benchmark/`;
- `artifact_readme` is the path to the artifact's README file that contains the step-by-step guide for preparing, installing, and running experiments;
- `artifact_url` the URL to the original artifact; 
- `evaluator` is a path to the evaluator's `main.py` entrypoint;
- `expected_score` is the total expected score for this artifact, which defaults to 4 as the agent is evaluated on it succesfully completing the four canonical AE stages (!!NOTE!! We encourage users not to change this value, unless they opt for another universal metric for artifact evaluation).
- `docker_evn` (optional) points to a Docker image on Docker Hub.

It also requires users to extend the artifact they plan to add with a self-contained evaluator in an `_agent_eval/` directory. This evaluator encodes *minimal*, objective success criteria for the four canonical AE stages and is what the benchmark actually calls.

Using WASABI's [agent evaluator](data/benchmark/sosp24_wasabi/wasabi/_agent_eval/) as a template, users will therefore need to extend the artifact with:

1. An `_agent_eval/` package which contains all benchmark-specific code and does *not* modify your original artifact logic.

2. One oracle module per stage. In this benchmark, each stage is typically implemented as a **derived oracle class** that overrides `requirements()` and returns an ordered list of programmatic checks (requirements). The base oracle handles running requirements, producing a structured report, printing a PASS/FAIL summary, and returning `True`/`False` from `run(verbose=...)`.

  A typical `_agent_eval/` layout looks like:

   ```text
   _agent_eval/
   ├── main.py
   ├── oracle_env_setup.py
   ├── oracle_build_install.py
   ├── oracle_prep_benchmark.py
   ├── oracle_run_experiments.py
   └── refs/
       ├── datasets.ref.json
       └── results.ref.json
   ```

   The `refs/` directory stores machine-checkable ground truth (e.g., dataset manifests/checksums, expected metric tables, or summaries of deterministic outputs) used by benchmark-prep and experiment-runs checks.

   Here is a simplified environment setup oracle (one dependency/version requirement):

   ```python
   # _agent_eval/oracle_env_setup.py
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

   Also, note that each oracle should be:
   - Non-interactive, meaning not expecting input or prompt interactions.
   - Idempotent, meaning safe to run multiple times without side-effects.
   - Time-bounded, meaning every command has a timeout.
   - Binary, meaning it returns pass/fail (as `True`/`False`) for the stage.

  For more details, check out this [how-to guide](src/evaluator/HOWTO.md)

1. A single `main.py` orchestrator, the entrypoint used by ArtEvalBench, which constructs an `EntryConfig`, invokes the four oracles in order, and returns an overall score (an integer between 0 and 4):

   ```python
   # _agent_eval/main.py
   import os
   from pathlib import Path

   from evaluator.utils import EntryConfig, LoggerConfig, get_logger, record_result

   from oracle_env_setup import OracleEnvSetup
   from oracle_build_install import OracleBuildInstall
   from oracle_prep_benchmark import OraclePrepBenchmark
   from oracle_run_experiments import OracleRunExperiments

   CONFIG = EntryConfig(
       name="my-artifact",
       home_dir=Path.home() / "artevalbench" / "my-artifact",
       repository_paths={
           "my-artifact": Path.home() / "artevalbench" / "my-artifact" / "repo",
       },
       results_paths={
           "results": Path.home() / "artevalbench" / "my-artifact" / "repo" / "outputs" / "results.json",
       },
       ground_truth_paths={
           "datasets": Path.home() / "artevalbench" / "my-artifact" / "_agent_eval" / "refs" / "datasets.ref.json",
           "results": Path.home() / "artevalbench" / "my-artifact" / "_agent_eval" / "refs" / "results.ref.json",
       },
       similarity_ratio=0.75,
   )

   def main(argv: list[str]) -> int:
       verbose = "--verbose" in argv
       logger = get_logger(
           LoggerConfig(root_name=os.environ.get("EVAL_LOGGER_NAME", "ARTEVAL-EVAL"))
       )

       results: dict[str, int] = {}
       score = 0

       score += record_result(
           results, "env_setup",
           OracleEnvSetup(config=CONFIG, logger=logger).run(verbose=verbose),
       )
       score += record_result(
           results, "build_install",
           OracleBuildInstall(config=CONFIG, logger=logger).run(verbose=verbose),
       )
       score += record_result(
           results, "prep_benchmark",
           OraclePrepBenchmark(config=CONFIG, logger=logger).run(verbose=verbose),
       )
       score += record_result(
           results, "run_experiments",
           OracleRunExperiments(config=CONFIG, logger=logger).run(verbose=verbose),
       )

       logger.info("Stage scores: %s", results)
       logger.info("FINAL_SCORE %d/4", score)
       return score

   if __name__ == "__main__":
       raise SystemExit(main([]))
   ```

   Note that the `ArtEvalBench` framework will invoke `main.py` to run the oracles in order, compute the agent's score for this particular artifact, and store it into a JSON file that aggregates these outcomes for the entire benchmark.

## Benchmark Setup

#### » Run the benchmark

To run the benchmark:

1. Execute the `run.sh` script with your model:

```sh
./run.sh <model_name>
# Example: ./run.sh claude-sonnet-4-5-20250929
```

2. Configure your LLM endpoint in `env.toml`:
* For Azure/OpenAI models: Set `AZURE_API_KEY`, `AZURE_API_BASE`, `AZURE_API_VERSION`
* For Anthropic models: Set `ANTHROPIC_API_KEY`
* For self-hosted models: Configure `OPENAI_API_TYPE` and `OPENAI_BASE_URL`

3. Results will be saved to `outputs/` with timestamp and model information

#### » Supported Agents

The benchmark supports multiple AI agents:
- **Claude Code**: Anthropic's code assistant
- **Mini SWE Agent**: The compact version of [SWE-agent](https://github.com/SWE-agent) assistant
- **OpenHands**: Open-source coding agent
- **ae_agent**: Claude Agent SDK–based agent (same logic as the standalone [artifact-agent](https://github.com/sys-intelligence/artifact-agent) repo), with full support for host/Docker, interactive mode, Skill, Sub-agent, per-task timeout, GPU, and optional container sync/commit/stop.

To add your own agent to the benchmark, see [add_agents.md](add_agents.md).

#### » ae_agent usage and options

When using the **ae_agent** (`-a ae_agent` or `-a ae-agent`), you can pass the following from the command line and/or the task JSONL.

**Command-line arguments**

| Argument | Description |
|----------|-------------|
| `-i`, `--input_file` | Input JSONL file with tasks (default: `./data/benchmark/arteval_tasks.jsonl`). |
| `-o`, `--save_path` | Directory for results (default: `./outputs/ae_<model>_ae-agent_<timestamp>`). |
| `-a`, `--agent` | Agent name; use `ae_agent` or `ae-agent` for this agent. |
| `-m`, `--model_name` | Model name (e.g. `claude-sonnet-4-5-20250929`). |
| `--interactive` | After the task completes, keep a session open so you can give more instructions (requires a TTY). In Docker mode the runner is executed in the foreground via `docker exec -it`. |
| `--enable-skill` | Enable Claude Agent SDK Skill (load from `~/.claude/skills/` and `.claude/skills/`). |
| `--enable-subagent` | Enable Claude Agent SDK Sub-agent (Task tool). |

**JSONL task fields (per line)**

| Field | Description |
|-------|-------------|
| `artifact_id` | Unique task identifier. |
| `artifact_dir` | Artifact directory name (relative to the JSONL file’s directory). |
| `artifact_readme` | Path to the README or task description file (relative to artifact root). |
| `artifact_url` | Optional. Git clone URL; used when `artifact_dir` is missing or the path does not exist. |
| `env` | `"local"` for host; Docker image name (e.g. `bastoica/ae-agent-ubuntu24.04:latest`) for Docker. |
| `evaluator` | Command to run after the agent (e.g. `python _agent_eval/main.py`). |
| `expected_score` | Expected score for this artifact (default 4). |
| `timeout` | Optional. Per-task timeout in seconds or milliseconds (see utils: values &lt; 86400 are seconds, else milliseconds). |
| `gpu` | Optional. When `true`, pass `--gpus all` to Docker (Docker mode only). |
| `interactive` | Optional. When `true`, enable interactive mode for this task (overrides CLI default). |
| `enable_skill` | Optional. When `true`, enable Skill for this task. |
| `enable_subagent` | Optional. When `true`, enable Sub-agent for this task. |
| `keep_container` | Optional. When `false` (default for ae_agent), after the run the workspace is synced from the container to the host, the container is committed as an image, and the container is stopped. When `true`, the container is left running for inspection. |

**Examples**

```sh
# Host mode, default options
python src/main.py -i ./data/benchmark/arteval_tasks.jsonl -a ae_agent -o ./outputs/run1

# With interactive mode (TTY required for Docker)
python src/main.py --interactive -i ./data/benchmark/arteval_tasks.jsonl -a ae_agent -o ./outputs/run2

# Enable Skill and Sub-agent
python src/main.py --enable-skill --enable-subagent -i ./data/benchmark/arteval_tasks.jsonl -a ae_agent -o ./outputs/run3
```

**Outputs (when using ae_agent)**

Results are written under the given `save_path`:

- `result.jsonl` — One JSON object per task (task_id, status, score, agent_run_results, etc.).
- `avg_score.json` — Benchmark summary (final_score, total_tasks).
- `ae_report_<artifact_id>.md` — Per-task report (status, project path, log file, agent summary, and optional Docker image instructions).
- `summary.json` — Total and successful task counts and success rate (same format as standalone artifact-agent).
- When running via the benchmark entry, log paths and agent summary are filled from available data; standalone `python -m ae_agent.main` also produces `ae_log_<artifact_id>.log`.

**Docker + interactive**

For Docker tasks with `interactive: true` (or `--interactive`), the benchmark runs the agent in the foreground via `docker exec -it` so you can interact in the same terminal. This requires a real TTY (e.g. running `python src/main.py ...` in a terminal, not under CI or with redirected stdin). If stdin is not a TTY, the run falls back to non-interactive (background runner) and a warning is logged.
