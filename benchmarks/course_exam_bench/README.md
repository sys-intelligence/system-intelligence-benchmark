# Course Exam Benchmark

This benchmark evaluates the performance of Large Language Models (LLMs) on system course exams.

- 69 questions from 5 MIT exams
- Question types: Single-choice, multiple-choice, true/false, and short-answer
- Includes real student performance data for comparison

For current model evaluation results, see [EVALUATION_RESULTS.md](EVALUATION_RESULTS.md).

| Exam                           | Questions | Topics              |
| ------------------------------ | --------- | ------------------- |
| MIT 6.5840 Spring 2025 Exam I  | 11        | Distributed Systems |
| MIT 6.5840 Spring 2025 Exam II | 15        | Distributed Systems |
| MIT 6.5840 Spring 2024 Exam I  | 15        | Distributed Systems |
| MIT 6.5840 Spring 2024 Exam II | 14        | Distributed Systems |
| MIT 6.1810 Fall 2024 Quiz II   | 14        | Operating Systems   |

## Quick Start

### 1. Install dependencies

```bash
./install.sh
```

This creates a Python virtual environment and installs required packages

### 2. Configure your LLM endpoint

Edit `env.toml` to add your API keys:

```toml
[llm]
AZURE_API_KEY = "your-key-here"
AZURE_API_BASE = "https://your-endpoint.openai.azure.com/"
# or
ANTHROPIC_API_KEY = "your-key-here"
```

### 3. Run the benchmark

```bash
./run.sh "gpt-4o"
```

Or run directly with Python:

```bash
source .venv/bin/activate
python src/main.py --model_name "gpt-4o"
```

### 4. Run tests

```bash
./test.sh
```

## How it works

1. Load questions: Reads exam questions from `data/benchmark/`
2. For each question:
   - Prompts the LLM with the question
   - Parses the LLM's JSON response
   - Evaluates the answer (exact match for multiple-choice, LLM-as-judge for short-answer)
   - Records the score
3. Generate summary: Aggregates results by exam and overall

## Output files

After running, you'll find results in `./outputs/course_exam__<model>__<timestamp>/`:

### 1. Per-question results (`results.jsonl`)

For each question, one JSON object per line:

```json
{
  "instance_id": 1,
  "exam_id": "6_1810_operating_system_engineering_fall_2024_quiz_ii",
  "question_type": "SingleChoice",
  "llm_answer": "C",
  "correct_answer": "C",
  "points_earned": 5,
  "points_possible": 5,
  "status": "correct"
}
```

Fields:

- `instance_id`: Question identifier
- `exam_id`: Exam identifier (links to exams_metadata.json)
- `question_type`: Type of question (`SingleChoice`, `MultipleChoice`, `True/False Questions`, `ShortAnswerQuestion`)
- `llm_answer`: LLM's answer
- `correct_answer`: Correct answer
- `points_earned`: Points the LLM earned
- `points_possible`: Maximum points for this question
- `status`: `correct`, `incorrect`, `partial`, or `error`

### 2. Full debugging information (`results_detailed.jsonl`)

Extended format with prompts and LLM explanations (for debugging).

### 3. Aggregated statistics (`summary.json`)

Overall performance and breakdown by exam with answered/unanswered/correct/incorrect counts.

### 4. LLM vs student performance (`comparison.json`)

Compares LLM performance against real student baseline data.

## Data format

The benchmark data is stored in `data/benchmark/`:

- `exams_metadata.json`: Exam-level metadata (one entry per exam)
- `questions.jsonl`: Individual questions (one JSON object per line that links to an exam from `exams_metadata.json` via `exam_id`)

## How to extend the benchmark

Consider this [MIT 6.824 Distributed Systems quiz](https://pdos.csail.mit.edu/6.824/quizzes/q25-2-sol.pdf). The steps below show how to add this exam to the benchmark. The same process applies to any course exam you want to include.

### Step 1: Add exam metadata to `exams_metadata.json`

Create a unique `exam_id` for your exam. Here's the actual entry for the Spring 2024 Exam II:

```json
{
  "exam_id": "6_5840_distributed_system_engineering_spring_2024_exam_ii",
  "test_paper_name": "6.5840 Distributed System Engineering: Spring 2024 Exam II",
  "course": "Distributed System Engineering",
  "year": 2024,
  "score_total": 71,
  "score_max": 71.0,
  "score_avg": 56.61,
  "score_median": 57,
  "score_standard_deviation": 9.13,
  "num_questions": 14
}
```

### Step 2: Add individual questions to `questions.jsonl`

Append your questions to the file. Each line is a JSON object. Here's an example from the exam (a True/False question about FaRM):

```json
{
  "instance_id": 33,
  "exam_id": "6_5840_distributed_system_engineering_spring_2024_exam_ii",
  "problem_num": 4,
  "points": 8,
  "problem": "# III FaRM  \n\nConsider the following statements about FaRM as described in No compromises: distributed transactions with consistency, availability, and performance. For each statement, circle True or False.  \n\n4. [8 points]:  \n\nTrue / False : Because FaRM uses primary-backup replication for a region (instead of Paxos), FaRM must reconfigure to remove a failed replica before FaRM can continue to use the region.  \n\nTrue / False : FaRM can use short leases (10ms by default) because it has communication and scheduling optimizations to renew leases quickly.  \n\nTrue / False : A transaction that modifies only one object will never abort.  \n\nTrue / False : Read-only transactions require only the validate step of the Commit phase in Figure 4.  ",
  "answer": "True,True,False,True",
  "explanation": "Answer: True, True, False, True. The first statement is true because FaRM requires a response from all replicas, thus it must reconfigure to remove the failed replica before it can continue with the affected shard. The third statement is false because another transaction may modify the one object causing this transaction's validation phase to fail (because the other transaction will have incremented the object's version number).",
  "type": "True/False Questions"
}
```

Required fields:

- `instance_id`: Globally unique number (use next available number)
- `exam_id`: Must match the `exam_id` from Step 1
- `problem_num`: Question number within the exam (1, 2, 3, ...)
- `points`: Points allocated to this question
- `problem`: The question text
- `answer`: Correct answer
  - For SingleChoice: `"A"`, `"B"`, etc.
  - For MultipleChoice: `"A,B,C"` (comma-separated, no spaces)
  - For True/False: `"True,False,True"` (one per sub-question)
  - For ShortAnswerQuestion: The model answer text
- `explanation`: Explanation of the correct answer
- `type`: One of `"SingleChoice"`, `"MultipleChoice"`, `"True/False Questions"`, `"ShortAnswerQuestion"`

> Note: Questions should be sorted by `exam_id` then `instance_id`

After adding the exam and questions, run `./test.sh` as a sanity check to valid the data format. This will also run in the CI pipeline.

## Question types and evaluation

| Type                 | Answer Format       | Evaluation Method | Partial Credit?                    |
| -------------------- | ------------------- | ----------------- | ---------------------------------- |
| SingleChoice         | `"A"`               | Exact match       | No                                 |
| MultipleChoice       | `"A,B,C"`           | Subset check      | Yes (2 points for partial correct) |
| True/False Questions | `"True,False,True"` | Exact match       | No                                 |
| ShortAnswerQuestion  | Free text           | LLM-as-judge      | Yes (scored 0 to max points)       |

For short-answer questions, an LLM evaluates the answer based on accuracy, completeness, logical consistency, and clarity.

## Training data templates

See the example files in:

- `data/sft/course_exam_sft_example.jsonl`: Format for supervised fine-tuning
- `data/pretrain/course_exam_pretrain_example.jsonl`: Format for pre-training
