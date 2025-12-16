<h1>SREGym: A Benchmarking Platform for SRE Agents</h1>

[🔍Overview](#🤖overview) |  [📦Installation](#📦installation) | [🚀Quick Start](#🚀quickstart) | [⚙️Usage](#⚙️usage) | [🤝Contributing](./CONTRIBUTING.md) | [📖Docs](https://sregym.com/docs) | [![Slack](https://img.shields.io/badge/-Slack-4A154B?style=flat-square&logo=slack&logoColor=white)](https://join.slack.com/t/SREGym/shared_invite/zt-3gvqxpkpc-RvCUcyBEMvzvXaQS9KtS_w)

## Overview
SREGym is an AI-native platform to enable the design, development, and evaluation of AI agents for Site Reliability Engineering (SRE). The core idea is to create live system environments for SRE agents to solve real-world SRE problems. SREGym provides a comprehensive SRE benchmark suite with a wide variety of problems for evaluating SRE agents and also for training next-generation AI agents.
<br><br>

![SREGym Overview](./sregym_core/assets/SREGymFigure.png)

SREGym is inspired by our prior work on AIOpsLab and ITBench. It is architectured with AI-native usability and extensibility as first-class principles. The SREGym benchmark suites contain 86 different SRE problems. It supports all the problems from AIOpsLab and ITBench, and includes new problems such as OS-level faults, metastable failures, and concurrent failures. See our [problem set](https://sregym.com/problems) for a complete list of problems.


In this README.md, I will quickly explain how to run SREGym within the System Intelligence Framework.

For advanced use of *System Intelligence* and *SREGym*, please refer to the docs of [*System Intelligence*](https://github.com/sys-intelligence/system-intelligence-benchmark/tree/main/doc) and [*SREGym*](https://sregym.com/docs)

## Architecture Explanation

### Abstraction

SREGym has a decoupled design which complies with *System Intelligence* philosophy.
Here is the correspondence of the components in *System Intelligence* and *SREGym*:

The `Executor` is the agent in *SREGym*, which is decoupled from the framework functionality. We have a baseline agent implementation in `sregym_core/clients/stratus/stratus_agent/` and it is run by default. If you want to bring your own agent, please follow the [Running Your Own Agent](https://sregym.com/docs/running-your-own-agent) guide.

The `Evaluator` is the evaluation oracles in *SREGym*, which is decoupled from the agent implementation. 

The*SREGym*'s `Conductor` serves as the `Environment` in *System Intelligence*.

### Task Details

- **Environment Setup**: SREGym Conductor will inject faults into the environment and lead to failures.
- **Diagnosis**: The agent will be asked to diagnose the root cause of the failure.
- **Mitigation**: The agent will be asked to mitigate the failure.
- **Evaluation**: The RCA result will be evaluated by the LLM as a judge oracle, and the mitigation result will be evaluated by specifically-designed mitigation oracles.


## Run SREGym

1. Prepare `sregym_core/.env` for the configurations. You can make a copy of `sregym_core/.env.example` into `sregym_core/.env` and set the keys in the `.env` file. For System Intelligence, you need to set the API keys for all the models you want to test, like below:

``` shell
GEMINI_API_KEY="XXXXXX"
OPENAI_API_KEY="XXXXXX"
ANTHROPIC_API_KEY="XXXXXX"
MOONSHOT_API_KEY="XXXXXX"
AZURE_API_KEY="XXXXXX"
AZURE_API_BASE="XXXXXX"

```
> If you want more pre-defined model configurations, please refer to the `sregym_core/llm_backend/configs.yaml` file and add your own configurations there. Then you can select the backend with cli argument `--model <model_id>`.

> For MS Azure and AWS Bedrock, you may need more configurations.


1. You need to make a `inventory.yml` file in the `sregym_core/scripts/ansible` directory. You can make a copy of `inventory.yml.example` into `inventory.yml` and set the hosts in the `inventory.yml` file. You can follow the instructions [here](https://github.com/SREGym/SREGym?tab=readme-ov-file#a-kubernetes-cluster-recommended) to get a cluster and set up the inventory file.

2. Install the dependencies
``` shell
cd benchmarks/sregym
./install.sh
```

3. Run the benchmark
``` shell
cd benchmarks/sregym
./run.sh <model_name> <agent_name>
```
> Some tested available names are: "gemini/gemini-2.5-flash", "openai/gpt-4o", "anthropic/claude-sonnet-4-20250514", "moonshot/moonshot-v1-32k".

The wrapper executes `python src/main.py --agent "stratus" --model_name "${MODEL_NAME}"` to run the benchmark.

The results will be saved in the `outputs/` directory.
``` shell
outputs/sregym__<model>__<agent>__<timestamp>/
├── avg_score.json     # Average score
└── result.jsonl       # Detailed results
```

## Use the System Intelligence CLI (optional)

To orchestrate SysMoBench alongside other benchmarks:

```bash
cd cli
./run_all_local.sh <model_name> <agent_name>
```

## How to Extend the Benchmark

Please refer to the [Adding New Components](https://sregym.com/docs/contributing#adding-new-components) guide in the SREGym documentation.

## Contribution

We strongly welcome contributions to SREGym.   
You can report bugs, suggest features, or contribute code to SREGym in the upstream repository [SREGym](https://github.com/SREGym/SREGym).
