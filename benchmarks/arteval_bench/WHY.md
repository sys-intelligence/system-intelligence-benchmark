# Why Artifact Evaluation as an AI Training Task?

`ArtEvalBenc`h` treats the artifact evaluation (AE) process as a training ground for AI agents to help form core [system intelligence capabilites](https://www.sigops.org/2025/defining-system-intelligence/). During AE, reviewers must reconstruct a target environment from incomplete specifications, build and configure complex software stacks with many implicit assumptions, prepare datasets and external benchmarks whose availability can change over time, run multi-stage experiments under strict resource and time constraints, and verify that reproduced results stay within acceptable margins of those reported in the paper. This makes AE a rich, realistic testbed for AI: agents must reason across all these steps, yet we believe they can be trained to reliably assist reviewers by automating most of this process.

Want to find out more or contribute? Take a look at our [contributor's guide](README.md).

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