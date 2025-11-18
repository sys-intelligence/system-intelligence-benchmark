# How to Create a Custom Benchmark

This guide will walk you through how to create a custom system-intelligence benchmark using the framework. By following these steps, you’ll be able to evaluate the latest models and agents on your own system-related tasks and seamlessly integrate your benchmark into the framework.

## Prerequisites

Before creating a custom benchmark, ensure you have:

- Python 3.9 or higher
- Basic understanding of the benchmark framework
- A clear evaluation task (tasks, how to score it) in mind

## Step 1: Create Your Benchmark Directory

Choose an example benchmark that **is similar to** your setting as a starting point. 

If your tasks involve exam-style questions, consider starting from [course_exam_bench](https://github.com/sys-intelligence/system-intelligence-benchmark/tree/main/benchmarks/course_exam_bench). If your benchmark focuses on algorithm design or optimization tasks, you might use [cache_algo_bench](https://github.com/sys-intelligence/system-intelligence-benchmark/tree/main/benchmarks/cache_algo_bench) as a template. These tasks can often be handled by a minimal agent (an LLM call plus a response parser).

Use [course_lab_bench](https://github.com/sys-intelligence/system-intelligence-benchmark/tree/main/benchmarks/course_exam_bench), if your benchmark is related to **environment setup, system understanding/implementation, performance analysis, or debugging tasks**, and each task may need different runing environments. These tasks typically require an LLM to autonomously call tools (such as the File Editor, Bash, etc.), navigate a large codebase, and run experiments or tests—similar to what a human developer would do. To support this, we provide several advanced agents (e.g., Claude Code, MiniSWEAgent) in this example, along with guidance for [integrating new agents](https://github.com/sys-intelligence/system-intelligence-benchmark/blob/main/benchmarks/course_lab_bench/add_agents.md).

1. Navigate to the benchmarks directory:

   ```bash
   cd benchmarks/
   ```

2. Copy the chosen benchmark to create your new benchmark:

   ```bash
   cp -r chosen_bench/ your_bench_name/
   cd your_bench_name/
   ```

3. Your benchmark directory should have the following mininal structure:

   ```
   your_bench_name/
   ├── src/
   │   └── main.py         # Main evaluation logic
   ├── data/               # Test data and scenarios
   │   └── benchmark/      # Benchmark datasets
   ├── tests/              # Unit tests
   ├── Dockerfile          # Docker configuration (optional)
   ├── env.toml            # Environment configuration
   ├── install.sh          # Installation script
   ├── run.sh              # Execution script
   ├── test.sh             # Testing script
   ├── requirements.txt    # Python dependencies
   └── README.md           # Benchmark documentation
   ```

## Step 2: Define Your Test Data

Create your evaluation dataset in a structured format:

1. Create a data directory if it doesn't exist:

   ```bash
   mkdir -p data/benchmark/
   ```

2. Define your test cases in JSONL format (recommended):

   The following is mininal example.
   ```jsonl
   {"id": "task_001", "sys_prompt": "You are a helpful assistant.", "user_prompt": "Solve this problem...", "response": "Expected answer..."}
   {"id": "task_002", "sys_prompt": "You are a helpful assistant.", "user_prompt": "Another task...", "response": "Expected answer..."}
   ```
   Each line contains:
   - `id`: Unique identifier for the test case
   - `sys_prompt`: System prompt for the LLM
   - `user_prompt`: User query/task description
   - `response`: Expected/ground truth response

3. **NOTES:** for more complex scenarios, you can use **any custom formats**. See [course_exam_bench](https://github.com/sys-intelligence/system-intelligence-benchmark/blob/main/benchmarks/course_exam_bench/data/benchmark/questions.jsonl) and [course_lab_bench](https://github.com/sys-intelligence/system-intelligence-benchmark/blob/main/benchmarks/course_lab_bench/data/benchmark/env_setup_examples.jsonl) for examples.

## Step 3: Select or Implement Your Executor and Evaluator

The `sdk/` folder provides base classes for building your benchmark. You need to select or implement both an **executor** (to run the LLM) and an **evaluator** (to score the results).

### 3.1 Review Available SDK Components

Check the `sdk/` folder for available components:

**Executors** (`sdk/executor.py`):
- `Executor`: Base class for executors
- `SimpleExecutor`: Basic LLM executor that extracts code from responses

**Evaluators** (`sdk/evaluator.py`):
- `Evaluator`: Base class for evaluators
- `BasicEvaluator`: Provides multiple similarity metrics (syntax correctness, exact match, Jaccard similarity, cosine similarity, embeddings similarity, LLM-as-judge)
- `ExamEvaluator`: Specialized for exam questions (single-choice, multiple-choice, short-answer)
- `LLMJudger`: Uses LLM to judge response quality
- `LLMExamJudger`: Uses LLM to grade exam responses

**Other utilities**:
- `sdk/llm.py`: LLM interface for querying language models
- `sdk/utils.py`: Utility functions including `set_llm_endpoint_from_config()`

### 3.2 Implement Your Main Evaluation Logic

Edit `src/main.py` to implement your benchmark. Here's the structure based on `example_bench`:

```python
"""Benchmark for evaluating model performance on your specific task."""

import argparse
import json
import os
import sys
from datetime import datetime

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../')))

from sdk.utils import set_llm_endpoint_from_config  
set_llm_endpoint_from_config('env.toml')

from sdk.executor import SimpleExecutor  
from sdk.evaluator import BasicEvaluator  


def main(_input_file, output_dir, _model_name, agent_name):
    """Main function for running the benchmark."""
    total_score = []

    with (
        open(_input_file, encoding='utf-8') as data,
        open(os.path.join(output_dir, 'result.jsonl'), 'w', encoding='utf-8') as output_file,
    ):
        for line in data:
            item = json.loads(line)
            print('============ ' + item['id'] + ' ============')

            # Step 1: Select or implement your executor
            if agent_name == "llm":
                executor = SimpleExecutor(_model_name, item['sys_prompt'])
            else:
                # You can add more agents/executors here
                # Example: CustomExecutor, AgentExecutor, etc.
                raise ValueError(f'Unknown agent name: {agent_name}')

            # Step 2: Execute the task
            response = executor.run(item['user_prompt'])

            # Step 3: Select or implement your evaluator
            evaluator = BasicEvaluator(_model_name)
            offline_metrics = evaluator.eval(
                question=item['user_prompt'],
                answer=response,
                groundtruth=item
            )

            # Step 4: Collect scores
            total_score.append((
                offline_metrics['syntax_acc'],
                offline_metrics['exact_match'],
                offline_metrics['jaccard_similarity'],
                offline_metrics['cosine_similarity'],
                offline_metrics['embeddings_similarity'],
                offline_metrics['llmjudger_rating'],
            ))

            # Step 5: Save individual result
            result = {
                'id': item['id'],
                'sys_prompt': item['sys_prompt'],
                'user_prompt': item['user_prompt'],
                'groundtruth': item['response'],
                'response': response,
                'syntax_acc': offline_metrics['syntax_acc'],
                'exact_match': offline_metrics['exact_match'],
                'jaccard_similarity': offline_metrics['jaccard_similarity'],
                'cosine_similarity': offline_metrics['cosine_similarity'],
                'embeddings_similarity': offline_metrics['embeddings_similarity'],
                'llmjudger_rating': offline_metrics['llmjudger_rating'],
                'llmjudger_answer': offline_metrics['llmjudger_answer'],
            }
            print('Evaluation Result:')
            print(result)
            output_file.write(json.dumps(result))
            output_file.write('\n')

    # Step 6: Calculate and save average scores
    avg_score = [sum(values) / len(values) for values in list(zip(*total_score))]
    avg_score_dict = {
        'syntax_acc': avg_score[0],
        'exact_match': avg_score[1],
        'jaccard_similarity': avg_score[2],
        'cosine_similarity': avg_score[3],
        'embeddings_similarity': avg_score[4],
        'llmjudger_rating': avg_score[5],
        'final_score': sum(avg_score[:5]) / 5,  # It's final score for your benchmark, you should customize it
    }
    with open(os.path.join(output_dir, 'avg_score.json'), 'w', encoding='utf-8') as avg_score_file:
        json.dump(avg_score_dict, avg_score_file, indent=4)
    print('************ Final average score ************')
    print(avg_score_dict)
```

### 3.3 Customization Options

**Option A: Use Existing SDK Components** (Recommended)

For standard evaluations, use the provided executors and evaluators:

```python
from sdk.executor import SimpleExecutor
from sdk.evaluator import BasicEvaluator  # or ExamEvaluator

executor = SimpleExecutor(model_name, sys_prompt)
evaluator = BasicEvaluator(model_name)
```

**Option B: Implement Custom Executor**

For specialized execution needs (e.g., code execution, agent-based reasoning):

```python
from sdk.executor import Executor

class CustomExecutor(Executor):
    def __init__(self, model_name, sys_prompt):
        super().__init__(model_name, sys_prompt)
        # Your custom initialization

    def run(self, user_prompt, lang=''):
        # Your custom execution logic
        # Example: run code, use specialized prompting, multi-turn dialogue
        pass
```

**Option C: Implement Custom Evaluator**

For specialized evaluation metrics:

```python
from sdk.evaluator import Evaluator

class CustomEvaluator(Evaluator):
    def __init__(self, model_name):
        super().__init__()
        self.model_name = model_name

    def eval(self, question, answer, groundtruth):
        # Your custom evaluation logic
        # Example: code execution validation, domain-specific metrics
        return {
            'custom_metric_1': score1,
            'custom_metric_2': score2,
        }
```

### 3.4 Examples from Existing Benchmarks

- **`example_bench/src/main.py`**: Uses `SimpleExecutor` + `BasicEvaluator` for basic evaluation with multiple similarity metrics
- **`course_exam_bench/`**: Uses `SimpleExecutor` + `ExamEvaluator` for grading exam questions
- **`cache_algo_bench/`**: Uses custom evaluator (cache_simulator) for code execution and performance testing
- **`course_lab_bench/`**: Uses agent-based executor for complex project execution

## Step 4: Configure Your Benchmark

### 4.1 Update `env.toml`

Configure your benchmark settings:

```toml
[llm]
OPENAI_API_KEY = "sk-XXXX"
AZURE_API_KEY = "XXX"
AZURE_API_BASE = "XXX"
AZURE_API_VERSION = "2024-05-01-preview"
ANTHROPIC_API_KEY = "sk-ant-XXXX"

[hardware]
use_gpu = false

[env-docker]
image = "default"  # or specify custom image
entrypoint = "run.sh"
```

### 4.2 Update `requirements.txt`

Add any additional dependencies your benchmark needs beyond the SDK requirements.

### 4.3 Update `install.sh`

Ensure all dependencies are installed:

```bash
#!/bin/bash

set -e

echo "Installing dependencies for your_bench_name..."

# You can add system-level dependencies here if needed

# Create virtual environment if needed
if [ ! -d "venv" ]; then
    python3 -m venv venv
fi

source venv/bin/activate

# Install requirements
pip install -r requirements.txt

echo "Installation complete!"
```

### 4.4 Update `run.sh`

Configure the execution script:

```bash
#!/bin/bash

set -e

# Activate virtual environment
source venv/bin/activate

# Run the benchmark
python src/main.py -m "your-model-name" -a llm

echo "Benchmark execution complete!"
echo "Results saved to: outputs/"
```

### 4.5 Update the `README.md` file with:

1. **Scenario Description**: Explain what your benchmark evaluates
2. **Task Details**: Describe input, output, and evaluation criteria
3. **Setup Instructions**: Docker and manual setup steps
4. **Example Results (optional)**: Show sample outputs or performance metrics

See the template in `benchmarks/example_bench/README.md` for structure.

## Step 5: Add Tests (Optional but Recommended)

Create tests in the `tests/` directory:

```python
# tests/test_evaluator.py
import unittest
from src.main import main

class TestYourBenchmark(unittest.TestCase):
    def test_evaluation(self):
        """Test benchmark evaluation."""
        # Implement test
        pass

if __name__ == "__main__":
    unittest.main()
```

Run tests:

```bash
./test.sh
```

## Step 6: Test Your Benchmark

### Local Testing

1. Install dependencies:

   ```bash
   ./install.sh
   ```

2. Configure `env.toml` with your LLM credentials

3. Run the benchmark:

   ```bash
   ./run.sh
   ```

### Docker Testing (optional)

1. Build the Docker image:

   ```bash
   docker build -t your_bench_name .
   ```

2. Run in Docker:

   ```bash
   docker run --rm your_bench_name
   ```

## Step 7: Integrate with CLI

To make your benchmark available through the SysCapBench CLI:

1. Update `cli/run_docker.sh` or /run_all_local.sh if needed

2. Your benchmark will now be accessible via:

   ```bash
   cd cli
   ./run_all_local.sh <model_name>
   # or
   ./run_docker.sh <model_name>
   ```

## Contributing Your Benchmark

Once your benchmark is complete and tested:

1. Ensure all tests pass
2. Update the main README.md to list your benchmark
3. Submit a pull request following the [contribution guidelines](README.md#contributing)

Your contributions help make the system intelligence benchmark more comprehensive, robust, and valuable for evaluating AI systems!


## Others

### Best Practices

1. **Use the SDK**: Leverage the evaluator and executor base classes in `sdk/` for consistency
2. **Standardized Output**: Follow the JSONL format for results and JSON for summaries
3. **Error Handling**: Implement robust error handling and timeouts
4. **Documentation**: Provide clear documentation and examples
5. **Reproducibility**: Ensure your benchmark produces consistent results
6. **Code Quality**: Follow the project's coding standards (Ruff, 120 char lines, Google-style docstrings). 
Follow the [PreChecks.md](PreChecks.md) for code formatting and linting guidelines.

### Examples

Refer to existing benchmarks for inspiration:

- **`example_bench/`**: Minimal template with `SimpleExecutor` + `BasicEvaluator`
- **`cache_algo_bench/`**: Code execution, algorithm simulation and performance evaluation
- **`course_exam_bench/`**: Multiple-choice and short-answer questions with `ExamEvaluator`
- **`course_lab_bench/`**: Complex project-based evaluation with agent executors

### Getting Help

- Review the main [README.md](README.md) for overall project structure
- Check the `sdk/` folder for available base classes and utilities
- Check existing benchmarks for implementation patterns
