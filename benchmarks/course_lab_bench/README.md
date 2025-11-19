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

## How to Extend the Benchmark

This section describes how to add additional labs to the benchmark. We show the workflow using the existing [MapReduce lab](http://nil.csail.mit.edu/6.5840/2024/labs/lab-mr.html) as an example:

### Step 1: Add a row to the CSV file

Edit `data/benchmark/lab_exam_data_20250529.csv` and add a new row. Here is what each column represents:

| Column            | Value                            | Description                                                |
| ----------------- | -------------------------------- | ---------------------------------------------------------- |
| `instance_id`     | `1`                              | Unique numeric ID for the task                             |
| `course`          | `6.5840: Distributed Systems`    | Course name                                                |
| `year`            | `Spring 2024`                    | Course term/year                                           |
| `index`           | `Lab 1: MapReduce`               | Lab name                                                   |
| `introduction`    | `In this lab you'll build...`    | Goes into markdown: Problem Context → Introduction         |
| `getting_started` | `You need to setup Go...`        | Goes into markdown: Getting Started section                |
| `The code`        | (starter code description)       | Goes into markdown: The Code section                       |
| `description`     | `Your job is to implement...`    | Goes into markdown: Your Task section                      |
| `repo`            | `6.5840-golabs-2024`             | Repository folder name (will be prefixed with `projects/`) |
| `test_method`     | `cd src/main && bash test-mr.sh` | Shell command to run tests                                 |
| `test_results`    | `*** PASSED ALL TESTS`           | Expected test output when solution is correct              |
| `difficluty`      | `moderate/hard`                  | Difficulty: `easy`, `moderate`, `moderate/hard`, or `hard` |
| `link`            | `http://.../lab-mr.html`         | URL to original course lab assignment                      |

### Step 2: Run the conversion script

```bash
cd data/benchmark
python3 convert_promblems.py
```

This generates:

- `problems/system_lab_<id>.md` - Markdown file with task description
- Updates `system_lab_tasks.jsonl` - JSONL with all tasks

### Step 3: Update `install.sh` (if adding a new repository)

```bash
if [ -d "6.5840-golabs-2024" ]; then
    echo "==> 6.5840-golabs-2024 already exists, skipping clone."
else
    echo "==> Cloning 6.5840-golabs-2024..."
    git clone git://g.csail.mit.edu/6.5840-golabs-2024
fi
```

### Step 4: Test your addition

```bash
./install.sh
./run.sh <model_name>
```
