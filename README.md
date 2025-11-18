# System Intelligence Benchmark: A Benchmark Suite for Evaluating LLM's System Capabilities

System Intelligence Benchmark is a comprehensive benchmark suite for evaluating the performance of Large Language Models (LLMs) and AI systems across critical system capabilities. It features tutorial, example benchmarks and offers both CLI tools and an SDK for further development.

## Benchmark Overview
A benchmark is a standard or point of reference against which things may be compared or assessed. In the context of AI and LLMs, benchmarks are essential for evaluating model capabilities, guiding research directions, and measuring progress. 

### Benchmark Framework

To advance benchmark development, we propose the System Intelligence Benchmark, a modular and extensible framework designed to support diverse research domains and problem types. As shown in the below figure, the framework comprises four abstractions: task set, environment, executor, and evaluator. Each task is associated with a specific environment, wherein the executor generates a solution that is subsequently assessed by the evaluator, which returns the evaluation metrics. This design enables the flexible integration of heterogeneous agents and their systematic evaluation. Additionally, the framework includes built-in executors (agents), evaluators (methodologies and grading rubrics), and tutorials. In an ideal case, users need only supply tasks that represent specific capabilities, select an evaluator, and quickly create and run a new benchmark. You can see [benchmark_abstraction.md](doc/benchmark_abstract.md) for details.

<img src="doc/benchmark.png" alt="Dashboard Screenshot" width="600"/>

The benchmark framework is **still under development**. If you have any questions, feel free to open an issue or contact us directly.  

### Benchmarks

System Intelligence Benchmark currently includes the following example benchmarks. Each benchmark assesses specific capabilities across multiple levels within a given research direction. Some benchmarks are still under development — we're actively updating them. Stay tuned!

- **System Exam Benchmark** ([benchmarks/course_exam_bench/](benchmarks/course_exam_bench/)) - Tests LLM understanding of system concepts through university course exams (54 questions across 4 exams)
- **System Lab Benchmark** ([benchmarks/course_lab_bench/](benchmarks/course_lab_bench/)) - Assesses AI capability on practical system course labs and projects 
- **System Artifact Benchmark** ([benchmarks/arteval_bench/](benchmarks/arteval_bench/)) - Evaluates AI performance on artifact evaluation
- **System Modeling Benchmark** ([benchmarks/sysmobench/](benchmarks/sysmobench/)) - Evaluates an agent's ability to produce correct TLA+ models for real-world concurrent and distributed systems, covering system capabilities across system comprehension, abstraction, and potentially tool fluency.
- **Example Benchmark** ([benchmarks/example_bench/](benchmarks/example_bench/)) - Template and reference implementation for creating new benchmarks

## Quick Start
### Repo Structure

- **Benchmarks** (`benchmarks/`) - Contains individual benchmark implementations, each with its own source code, tests, and configuration
- **CLI Tools** (`cli/`) - Command-line interface for running benchmarks and managing evaluations
- **SDK** (`sdk/`) - Software development kit providing evaluators, LLM interfaces, and utility functions
- **Documentation** (`doc/`) - Guides and documentation for using and contributing to SysCapBench

### Prerequisites

- Python 3.9+
- Docker (optional, for containerized execution)

> Docker images currently only support x86_64/AMD64 architecture. ARM64 (Apple Silicon M1/M2/M3) is not yet supported

### Installation

1. Clone the repository:

   ```bash
   git clone https://github.com/sys-intelligence/system_intelligence_benchmark.git
   cd system_intelligence_benchmark
   ```

2. Install dependencies for a specific benchmark:

   ```bash
   cd cli
   ./install.sh
   ```
3. Each benchmark includes an `env.toml` file for configuration. You should add your own llm endpoint url and key there.

### Running Benchmarks

#### Run All Benchmarks

To run all benchmarks sequentially:

```bash
cd cli
./run_all_local.sh <model_name>
```

#### Run a Single Benchmark

To run just one benchmark locally:

```bash
cd benchmarks/<benchmark_name>
./install.sh  # Only needed the first time
./run.sh <model_name>
```

#### Output Format

Benchmarks generate standardized outputs in `cli/outputs/{benchmark_name}__{model_name}__{agent}_{timestamp}/`:

- `result.jsonl`: Detailed evaluation results
- `summary.json`: Aggregated performance metrics
- Test-specific breakdowns and comparisons

You can find more detailed usage guides in the CLI [README.md](cli/README.md).

## Contribute to Benchmarks

We welcome community contributions to enrich existing benchmarks (e.g., by adding more exam problems to the System Exam benchmark and more system artifacts to System Artifact and System Modeling benchmark), port your existing benchmarks, and more importantly to create new system intelligence benchmarks with our framework. See below for detailed instructions. We believe that such collective community efforts will advance AI to its next level and help realize System Intelligence, unlocking the potential of AI-driven computing system innovations. If you are interested in contributing or already have good system benchmarks, please let us know. We have set up a [slack channel](https://join.slack.com/t/sys-intelligence/shared_invite/zt-3hpkgr2aa-NnuPxUbyHr45S89DFi_N1A) at sys-intelligence.slack.com.

> [!NOTE] 
> We suggest getting starting by walking through the basic concept of a AI benchmark: [Benchmark Abstraction](doc/benchmark_abstract.md). After understanding the basic concept, you can decide whether to Contribute to Existing Benchmarks, Porting Existing Benchmarks, or  Creating New Benchmarks.

### Contribute to Existing Benchmarks
The easiest way to contribute is to add more tasks to existing benchmarks. Currently, the following two are highly recommended. You can simply follow the provided guidelines to submit your data—once that’s done, you’re all set.
- **SystemExam**: If you are a professor teaching one or more courses, we highly recommend contributing **more exam problems** to SystemExam (see [this doc](https://github.com/sys-intelligence/system_intelligence_benchmark/tree/main/benchmarks/course_exam_bench#how-to-extend-the-benchmark) for step-by-step guidance).
- **SystemArtifact**: If you are a researcher submitting artifacts, or an AE chair involved in artifact evaluation, we highly recommend contributing **more system artifacts** to SystemArtifact (see [this doc](https://github.com/sys-intelligence/system_intelligence_benchmark/blob/main/benchmarks/arteval_bench/README.md) for step-by-step guidance).

In addition, you can also help review the existing benchmarks to propose improvement ideas or directly enhance them—for example, by adding more advanced evaluators or incorporating improved metrics.

### Porting Existing Benchmarks
> [!NOTE]
> See [porting_benchmark.md](doc/porting_benchmark.md) for step-by-step guidelines.

For integrating existing, independently-developed benchmark projects while maintaining synchronization with upstream:

- Use Git Subtree/Submodule to incorporate upstream code
- Write a bridge layer to connect upstream evaluators with framework SDK
- Configure bidirectional sync for pulling updates and contributing fixes

**Example:** [SysMoBench](benchmarks/sysmobench/) - ported from [SysSpecBench](https://github.com/specula-org/SysSpecBench)

### Creating New Benchmarks
> [!NOTE]
> See [custom_benchmark.md](doc/creating_benchmark.md) for step-by-step guidelines.

To create a new benchmark, follow these steps:
1. Create a new benchmark directory in `benchmarks/`
   1. Based on your specific requirements, select and copy an example benchmark as a starting point
   2. Update the `src/main.py` file with your specific evaluation logic (your executor and evaluator)
   3. Add test cases in the `tests/` directory
2. Update the README.md with benchmark-specific details
3. Implement `install.sh` and `run.sh` scripts
4. Update the benchmark list in `run_all_local.sh` and `run_docker.sh` if needed

## Contributing

This project welcomes contributions and suggestions.  Most contributions require you to agree to a
Contributor License Agreement (CLA) declaring that you have the right to, and actually do, grant us
the rights to use your contribution. For details, visit https://cla.opensource.microsoft.com.

When you submit a pull request, a CLA bot will automatically determine whether you need to provide
a CLA and decorate the PR appropriately (e.g., status check, comment). Simply follow the instructions
provided by the bot. You will only need to do this once across all repos using our CLA.

This project has adopted the [Microsoft Open Source Code of Conduct](https://opensource.microsoft.com/codeofconduct/).
For more information see the [Code of Conduct FAQ](https://opensource.microsoft.com/codeofconduct/faq/) or
contact [opencode@microsoft.com](mailto:opencode@microsoft.com) with any additional questions or comments.

## Trademarks

This project may contain trademarks or logos for projects, products, or services. Authorized use of Microsoft 
trademarks or logos is subject to and must follow 
[Microsoft's Trademark & Brand Guidelines](https://www.microsoft.com/en-us/legal/intellectualproperty/trademarks/usage/general).
Use of Microsoft trademarks or logos in modified versions of this project must not cause confusion or imply Microsoft sponsorship.
Any use of third-party trademarks or logos are subject to those third-party's policies.
