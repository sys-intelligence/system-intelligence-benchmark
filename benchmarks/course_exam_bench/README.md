# Course Exam Benchmark

This benchmark evaluates the performance of Large Language Models (LLMs) on system course exams.

- 69 questions from 5 MIT exams
- Question types: Single-choice, multiple-choice, true/false, and short-answer
- Includes real student performance data for comparison

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
  "exam_id": "6_1810_fall_2024_quiz_ii_solutions",
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

### Step 1: Add exam metadata to `exams_metadata.json`

Create a unique `exam_id` for your exam:

```json
{
  "exam_id": "your_university_course_year_semester_exam",
  "test_paper_name": "Your University Course Name: Semester Year Exam",
  "course": "Course Name",
  "year": 2025,
  "score_total": 100,
  "score_max": 95.0,
  "score_avg": 75.0,
  "score_median": 77.0,
  "score_standard_deviation": 10.5,
  "num_questions": 10
}
```

### Step 2: Add individual questions to `questions.jsonl`

Append your questions to the file. Each line is a JSON object:

```json
{
  "instance_id": 70,
  "exam_id": "your_university_course_year_semester_exam",
  "problem_num": 1,
  "points": 10,
  "problem": "Explain the difference between a process and a thread.",
  "answer": "A process is an instance of a running program with its own memory space, while a thread is a unit of execution within a process that shares the process's memory.",
  "explanation": "Full explanation here...",
  "type": "ShortAnswerQuestion"
}
```

Required fields:

- `instance_id`: Globally unique number (use next available number, currently 70+)
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
