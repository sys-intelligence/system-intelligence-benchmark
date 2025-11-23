# ArtEvalBench

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

2. One oracle module per stage, implemented in four distinct Python files each checking one of the four canonical stages of artifact evaluation. A typical oracle module looks as follows (simplified):
   ```python
   # _agent_eval/env_setup.py
   import subprocess
   from pathlib import Path

   def check() -> bool:
       # Example: verify virtualenv exists
       if not Path("venv").exists():
           print("Missing venv/ directory")
           return False

       # Example: verify Python version inside the venv
       proc = subprocess.run(
           ["venv/bin/python", "--version"],
           capture_output=True,
           text=True,
       )
       print(proc.stdout.strip())
       return proc.returncode == 0 and proc.stdout.startswith("Python 3.10")
    ```
    Also, note that each oracle should be:
    - Non-interactive, meaning not expecting input or prompt interactions.
    - Idempotent, meaning safe to run multiple times without side-effects.
    - It returns `True` or `False` based on the validation outcome and prints a brief diagnostic message.

3. A single `main.py` orchestrator, the entrypoint used by ArtEvalBench, which invokes the four oracle modules, runs them in order, and returns an overall score (an integer between 0 and 4):
    ```python
    # _agent_eval/main.py
    from . import env_setup, build_install, prep_benchmark, run_experiments

    def main() -> int:
        score = 0
        stages = [
            ("env_setup", env_setup.check),
            ("build_install", build_install.check),
            ("prep_benchmark", prep_benchmark.check),
            ("run_experiments", run_experiments.check),
        ]

        for name, check in stages:
            try:
                ok = bool(check())
            except Exception as e:
                print(f"[{name}] FAILED with exception: {e}")
                ok = False

            if ok:
                print(f"[{name}] PASSED")
                score += 1
            else:
                print(f"[{name}] FAILED")

        print(f"FINAL_SCORE {score}/4")
        return score

    if __name__ == "__main__":
        raise SystemExit(main())
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

To add your own agent to the benchmark, see [add_agents.md](add_agents.md).
