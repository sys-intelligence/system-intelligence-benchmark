# SREGym Quick Guide

In this README.md, I will quickly explain how to run SREGym within the System Intelligence Framework.

For advanced use of *System Intelligence* and *SREGym*, please refer to the docs of [*System Intelligence*](https://github.com/sys-intelligence/system-intelligence-benchmark/tree/main/doc) and [*SREGym*](https://sregym.com/docs)

## Architecture Explanation

SREGym has a decoupled design which complies with *System Intelligence* philosophy.
Here is the correspondence of the components in *System Intelligence* and *SREGym*:

The `Executor` is the agent in *SREGym*, which is decoupled from the framework functionality. We have a baseline agent implementation in `sregym_core/clients/stratus/stratus_agent/` and it is run by default. If you want to bring your own agent, please follow the [Running Your Own Agent](https://sregym.com/docs/running-your-own-agent) guide.

The `Evaluator` is the evaluation oracles in *SREGym*, which is decoupled from the agent implementation. 

The*SREGym*'s `Conductor` serves as the `Environment` in *System Intelligence*.

## Run SREGym

1. Prepare `.env` for the configurations. You can make a copy of `.env.example` into `.env` and set the keys in the `.env` file. For System Intelligence, you need to set the API keys for the models you want to test, like below:

``` shell
PROVIDER_TOOLS="litellm"
PROVIDER="litellm"

GEMINI_API_KEY="XXXXXX"
OPENAI_API_KEY="XXXXXX"
ANTHROPIC_API_KEY="XXXXXX"
MOONSHOT_API_KEY="XXXXXX"
```
> You do not need to set the `MODEL_TOOLS` in the `.env` file. It will be set automatically by the System Intelligence Framework. It is indented for individual run of SREGym.

2. You need to make a `inventory.yml` file in the `sregym_core/scripts/ansible` directory. You can make a copy of `inventory.yml.example` into `inventory.yml` and set the hosts in the `inventory.yml` file. You can follow the instructions [here](https://github.com/SREGym/SREGym?tab=readme-ov-file#a-kubernetes-cluster-recommended) to get a cluster and set up the inventory file.

3. Install the dependencies
``` shell
cd benchmarks/sregym
./install.sh
```

4. Run the benchmark
``` shell
cd benchmarks/sregym
./run.sh <model_name>
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
./run_all_local.sh <model_name>
```

## Contribution

We strongly welcome contributions to SREGym.   
You can report bugs, suggest features, or contribute code to SREGym in the upstream repository [SREGym](https://github.com/SREGym/SREGym).
