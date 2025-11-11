# System Intelligence Benchmark: A Benchmark Suite for Evaluating LLM's System Capabilities

It is a comprehensive benchmarking framework for evaluating the performance of Large Language Models (LLMs) and AI systems across critical system capabilities. It features example benchmarks for system course exams, course projects, and cache algorithm design, and offers both CLI tools and an SDK for further development.

## Benchmark Overview
### Benchmark Concept
A benchmark is a standard or point of reference against which things may be compared or assessed. In the context of AI and LLMs, benchmarks are essential for evaluating model capabilities, guiding research directions, and measuring progress. The following figure illustrates the main components of a AI benchmark. We abstract the benchmark into 4 components: the taskset, the environment, the executor, and the evaluator. This abstraction ensures a clear flow from tasks to metrics. You can see [benchmark_abstraction.md](doc/benchmark_abstract.md) for details.

<img src="doc/benchmark.png" alt="Dashboard Screenshot" width="600"/>

### Benchmarks

System Intelligence Benchmark currently includes the following example benchmarks. Some examples are still under development — we're actively updating them. Stay tuned!
- **Course Exam Benchmark** ([benchmarks/course_exam_bench/](benchmarks/course_exam_bench/)) - Tests LLM understanding of system concepts through university course exams (54 questions across 4 exams)
- **Course Project Benchmark** ([benchmarks/course_project_bench/](benchmarks/course_project_bench/)) - Assesses AI capability on practical system course projects
- **Cache Benchmark** ([benchmarks/cache_bench/](benchmarks/cache_bench/)) - Evaluates AI performance on cache algorithm design tasks
- **ArtEval Benchmark** ([benchmarks/arteval_bench/](benchmarks/arteval_bench/)) - Evaluates AI performance on writing Kusto Query Language (KQL) queries for platform operations
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

### Installation

1. Clone the repository:

   ```bash
   git clone https://github.com/systemintelligence/system_intelligence_benchmark.git
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

## Adding Benchmarks

> [!NOTE] 
> We suggest getting starting by walking through the basic concept of a AI benchmark: [Benchmark Abstraction](doc/benchmark_abstract.md).

After understanding the basic concept, you can decide whether to add more tasks for existing benchmarks or create new benchmarks that map to different levels of system capabilities.

### Contribute to existing Benchmarks
The easiest way to contribute is to add more tasks to existing benchmarks. For example, you can add more questions to the course exam benchmark or more projects to the course project benchmark. You can add more system algorithm design problems into algorithm design benchmark. Please follow the existing format and structure for adding new tasks. You can also improve the existing benchmarks by adding more advanced evaluators with improved metrics.

### Creating New Benchmarks
> [!NOTE] 
> See [custom_benchmark.md](doc/custom_benchmark.md) for step-by-step guidelines.

To create a new benchmark, follow these steps:
1. Create a new benchmark directory in `benchmarks/`
   1. Based on your specific requirements, copy an example benchmark as a starting point
   2. Update the `src/main.py` file with your specific evaluation logic
   3. Update the README.md with benchmark-specific details
   4. Add test cases in the `tests/` directory
2. Add an `env.toml` configuration file
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
