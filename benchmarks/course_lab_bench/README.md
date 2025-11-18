# Course Lab Benchmark [Under Development]

## Scenario Description

This benchmark evaluates AI agents on their ability to complete systems course labs and projects, particularly from MIT's 6.5840 (Distributed Systems). The benchmark tests agents on realistic system assignments that require:

- Understanding complex codebases written in Go
- Implementing distributed systems concepts (MapReduce, Raft, key-value stores)
- Working with database internals (storage, query execution)
- Writing concurrent, race-free code
- Passing comprehensive test suites

### Task Details

- **Input**: JSON/JSONL files containing:
  - Task descriptions from course lab assignments
  - Repository information (URLs, paths)
  - Docker environment specifications
  - Test methods and expected results
  - Links to original course materials

- **Output**:
  - Implementation code that passes provided test suites
  - Evaluation results with pass/fail status
  - Execution logs and error reports
  - Performance metrics stored in `outputs/` directory

- **Evaluation**:
  - Automated testing via course-provided test scripts
  - Binary pass/fail based on test suite results
  - Support for multiple test scenarios (sequential, concurrent, crash recovery)
  - Evaluation can run in Docker containers or manually

## Dataset

The benchmark includes tasks from:
- **6.5840 Distributed Systems Labs**: MapReduce, Raft consensus, fault-tolerant key-value service
- **Environment Setup Tasks**: Project configuration and dependency management

Files:
- `data/benchmark/course_lab_task_examples.jsonl` - Course lab examples
- `data/benchmark/env_setup_examples.jsonl` - Env Setup examples
- `data/benchmark/course_lab_tasks_mit_65840.jsonl` - System tasks from 6.5840 Distributed Systems 2024/2025

## Benchmark Setup

#### Install Dependencies

1. Run the `install.sh` script to set up the environment:

   ```sh
   ./install.sh
   ```

   This will:
   - Install Python 3.12 virtual environment
   - Clone and install SWE-agent
   - Install required Python packages (pytest, pytest-cov)
   - Clone course repositories (6.5840-golabs-2024, xv6-labs-2024, etc.)

#### Run

To run the benchmark:

1. Execute the `run.sh` script with your model:

   ```sh
   ./run.sh <model_name>
   # Example: ./run.sh claude-sonnet-4-5-20250929
   ```

2. Configure your LLM endpoint in `env.toml`:
   - For Azure/OpenAI models: Set `AZURE_API_KEY`, `AZURE_API_BASE`, `AZURE_API_VERSION`
   - For Anthropic models: Set `ANTHROPIC_API_KEY`
   - For self-hosted models: Configure `OPENAI_API_TYPE` and `OPENAI_BASE_URL`

3. Results will be saved to `outputs/` with timestamp and model information


## Supported Agents

The benchmark supports multiple AI agents:
- **Claude Code**: Anthropic's code assistant
- **OpenHands**: Open-source coding agent

To add your own agent to the benchmark, see [add_agents.md](add_agents.md).

