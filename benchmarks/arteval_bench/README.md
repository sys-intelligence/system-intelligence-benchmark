# ArtEvalBench

`ArtEvalBench` is a benchmark for evaluating AI agents that support the Artifact Evaluation (AE) process by auditing research prototypes (artifacts) that accompany research papers, as part of the peer-review process. Artifact evaluation involves reconstructing a reference environment from (partial) specifications, building and configuring complex codebases with often implicit assumptions, preparing datasets and third-party benchmarks whose availability may change over time, orchestrating multi-stage experiments under controlled resource and time budgets, and validating that observed results fall within acceptable tolerance bounds relative to those reported in the paper. Despite the intricacy of the process, we believe AI agents can be trained to support reviewers in evaluating artifacts that accompany research papers by automating most of these stages.

Want to find out more or contribute? Jump to the [contributor's guide](#contributors-guide).

## Goals and Objectives

Artifact evaluation has become a standard component of the peer-review process across a wide range of conferences in Computer Science, especially in Systems and related areas. Despite this progress however, the practical work of provisioning operational environments, resolving dependencies, building artifacts, preparing benchmarks, running experiments, and checking results remains brittle and time-consuming. To alleviate this burden, we envision an automated artifact evaluation AI assistant that executes repeatable steps under (human) reviewer supervision. This "AE assistant" would target artifact mechanics (e.g., code compilation, dataset/benchmark preparation, experiment orchestration, and output validation) alongside code auditing (e.g., does the artifact implementation match the paper prose? are results closely matching those in the paper?). The agent's output can then inform more a complex methodological assessment, design trade-off analysis, and results interpretation that reviewers need to perform to complete the AE process.

Concretely, given an artifact (code, documentation, experiment framework), a complete installation & operation guide, and the paper itself, the AE assistant:

1. provisions the reference environment;

2. builds/installs a particular version of the artifact using the specified toolchain;

3. retrieves and prepares datasets or other third-party targets;

4. orchestrates experiments with explicit configuration, time and resource budgets; and

5. generates a human-readable report that summarizes the outcome of each step, indicating any blockers (e.g., install missing dependencies) and how it managed to overcome them.

The goal is to reduce reviewer effort on mechanical tasks so attention can shift to scientific auditing.

## Background

#### » The artifact evaluation process

Most conferences award badges to incentivize high-quality artifacts that support the paper's claims by asking authors to participate in a multi-stage evaluation process where reviewers attempt to download, install, and operate the artifacts themselves. The following summarizes the widely used criteria for each badge:

* Artifact Available. This badge indicates that the artifact itself (code, documentation, scripts, benchmarks, etc.) is publicly accessible with a persistent identifier (e.g., DOI, commit ID) on an (ideally, long-term) archival repository (e.g., Zenodo, Github). Availability does not imply the artifact can compile, build, or is functionally correct. It only confirms that the materials needed to verify key claims, reproduce experimental results, and reuse the tool itself are open-sourced.

* Artifact Functional. This badge indicates that the artifact installs/builds in a reference environment and runs at least a subset of the documented experiments. It confirms that dependencies and configurations are explicitly recorded, and outputs, at least for said subset of experiments, are consistent with the paper's prose.

* Results Reproduced. This badge indicates that a third party can re-execute all necessary experiments to obtain results consistent with the paper, with a reasonable degree of tolerance (e.g., within relative error bounds, confidence intervals, or rank-ordering equivalence). On top of re-obtaining results that support the paper's claims, reproducibility further requires verifiable provenance (e.g., SW/HW environment characteristics, configuration parameters, experiment logs) and principled handling of non-determinism (e.g., repeated trials, fixed initial states, or variance analysis).

Further reading and a detailed description of criteria for each badge can be found [here](https://sysartifacts.github.io/eurosys2026/badges) and [here](https://sysartifacts.github.io/evaluator-guide.html).

#### » What makes AE challenging in practice?

Reproducibility and reusability can be obstructed by multiple factors including, but not limited to: (i) environment drift (e.g., legacy libraries no longer available, drivers mismatch in newer OS versions); (ii) undocumented or implicit build assumptions (e.g., hard-coded compiler flags, directory paths, IPs, or reliance on OS-wide libraries that differ across distributions); (iii) brittle preprocessing of third-party benchmarks or datasets (e.g., broken download URL, non-deterministic compilation steps that silently invalidate subsequent stages); and (iv) unspecified results tolerance bounds that complicate validation for non-deterministic experiments (e.g., performance claims without clarifying what constitutes an acceptable deviation when running within a similar SW/HW setup).

Overcoming such challenges require persistence and careful bookkeeping, precisely where an automated AE assistant can provide leverage.

## Contributor's guide

#### » Overview and high-level structure

To train and improve AE agents in a principled way we introduce `ArtEvalBench`, a curated collection of artifacts accompanying peer-reviewed papers. To ensure a fair comparison we include artifacts that have been already evaluated in an official AE process and awarded all three badges by the committee. Each entry includes the original artifact (instructions, code, scripts, datasets/benchmarks, etc.), the original paper, and a collection of "oracle" scripts that define objective checkpoints at four canonical stages: environment setup, build/install, benchmark preparation, and experiment execution.

`ArtEvalBench` is designed to evaluate agents on capability (which stages they complete), efficiency (wall-clock time and intervention count), and fidelity (how closely reproduced results match those reported).

To check those capabilities, each artifact includes four oracle scripts that encode minimal, verifiable success criteria for each of the four stages. The oracles are invoked non-interactively and must be idempotent. Conceptually, these for stages correspond to:

1. Environment Setup: verifies presence and versions of required tools, libraries, or other dependencies; confirms hardware availability when applicable; and checks that configurations are portable rather than hardcoded or tied to a specific machine.
2. Build/Install: confirms a complete build (or install) operation from a specified version, with expected binaries/modules present; running tests, when available, or simple validation commands like invoking `--help` or equivalent.
3. Benchmark Preparation: asserts that datasets/benchmarks are present and checksums match; verifies that necessary third-party tools compile and the artifact's instrumentation/monitoring hooks are enabled, if applicable.
4. Experiment Runs: executes each experiment according to the authors' guidelines; checks that the artifact produces the expected metrics, logs, files, figures, etc.; provides an initial assessment relative to specified tolerance bounds.

For a typical example, check out the [agent evaluator](data/benchmark/sosp24_wasabi/wasabi/_agent_eval/) of [WASABI](data/benchmark/sosp24_wasabi/wasabi/).

#### » Adding a new artifact

Adding a new artifact to the benchmark requires several steps:

1. Create a stand-alone directory in `./data/benchmark` and copying all artifact files including the README file.
2. Implement oracles for evaluating the AI agent. This feature should follow the same structure as Wasabi's [evaluator](data/benchmark/sosp24_wasabi/wasabi/_agent_eval/), where each oracle is implemented in a separate Python source file and orchestrated by a `main.py` whose `main()` method returns a single integer, the overal score (0..4) the agent achieved.
3. Create an entry into the [task journal](data/benchmark/arteval_tasks.jsonl) and populate the appropriate fields.

## Benchmark Setup

#### » Install dependencies

To install the benchmark, simply run the `install.sh` script to set up the environment:
 ```sh
 ./install.sh
 ```

 This operaiton will:
 * Install Python 3.12 virtual environment
 * Clone and install SWE-agent
 * Install required Python packages (pytest, pytest-cov)
 * Clone course repositories (6.5840-golabs-2024, xv6-labs-2024, etc.)

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
* **Claude Code**: Anthropic's code assistant
* **Mini SWE Agent**: The compact version of [SWE-agent](https://github.com/SWE-agent) assistant
* **OpenHands**: Open-source coding agent

To add your own agent to the benchmark, see [add_agents.md](add_agents.md).
