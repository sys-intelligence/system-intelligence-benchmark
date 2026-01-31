# Course Exam Benchmark

A benchmark for evaluating AI agents on systems course exam questions. This benchmark tests AI agents' ability to answer technical exam questions covering topics like operating systems, distributed systems, databases, and networking.

> Leaderboard hosted on HuggingFace Spaces: [sys-intelligence/leaderboard](https://huggingface.co/spaces/sys-intelligence/leaderboard)

## What is this benchmark?

This benchmark is designed for standalone exam questions similar to traditional paper exams. Think of this as a closed-book exam with an optional cheatsheet where students solve questions using only pen and paper (no code execution, no file system access, no web browsing, or any other agent actions).

What's allowed:

- Plain text questions (single choice, True/False, short answer, etc.)
- Reference materials (markdown files serving as cheatsheets)

What's not allowed:

- Questions requiring code execution
- Questions requiring file system interaction
- Questions requiring web access or external tools
- Any form of agent execution beyond reading and answering
- Questions with images/figures (see policy below)

> We understand that different professors and universities use different terminology (e.g., "take-home exam," "assignments" instead of "labs"), but the line we draw is that the exam benchmark only includes plain text questions with optional reference markdown files. If a question requires any form of execution, environment setup, or interactive problem-solving, it belongs in the [Course Lab Benchmark](../courselab_bench/) instead.

## Running Evaluation

This benchmark uses [Inspect](https://inspect.ai-safety-institute.org.uk/) for evaluation. After preparing the dataset, you can run evaluations with different models and configurations.

```bash
# Install the benchmark
pip install -e .

# Prepare the dataset (run this once after adding new exams)
python prepare_dataset.py

inspect eval courseexam --model openai/gpt-4

# Filter by exam
inspect eval courseexam -T exam_ids=example_course_2024_midterm --model openai/gpt-4

# Filter by question type (ExactMatch or Freeform)
inspect eval courseexam -T question_types=ExactMatch --model openai/gpt-4

# Filter by tags
inspect eval courseexam -T tags=operating-systems --model openai/gpt-4

# Use a different judge model for Freeform questions
inspect eval courseexam -T judge_model=openai/gpt-4o --model openai/gpt-4

# If you prefer to modify the configuration in code, edit run_eval.py then run:
python run_eval.py
```

After running evaluations, view results with:

```bash
inspect view
```

## Adding New Exams

Exams are written in markdown format and automatically converted using `prepare_dataset.py`.

### Markdown Format

See [data/raw/example_course_2024_midterm/exam.md](data/raw/example_course_2024_midterm/exam.md) for a complete example with comments explaining each question type.

Format overview:

- JSON block at the top for exam metadata
- Questions separated by `---`
- Question text in markdown
- JSON block for question metadata and answer
- Optional `comments` field for notes about the question

### Steps to Add an Exam

1. Create a new folder in `data/raw/`: `data/raw/your_exam_name/`
2. Create `exam.md` in that folder following the format
3. (Optional) Add reference materials (`.md` files) to the same folder
4. Run the preparation script: `python prepare_dataset.py`

The script will automatically parse your markdown and generate `data/questions.jsonl` and `data/exams_metadata.json`. It will also copy any reference materials to `data/reference_materials/`.

### Handling Multi-Part Questions

Each question should be standalone. The `problem_id` field is flexible and supports values like `2.1` or `4a` for subquestions.

If multiple subquestions share the same context, you have two options:

- Separate questions: Create individual questions with their own JSON blocks. Make sure to include the shared context in each question's text.
- Combined question: Merge subquestions into one question (JSON). Ask for a comma-separated list of answers (e.g., `"A, B, D"`) for `ExactMatch`, or use `Freeform` with an LLM judge for more complex grading.

## Question Types

ExactMatch: Questions with one correct answer, graded by exact string match

- Single choice (A/B/C/D)
- True/False

Freeform: Free-form text questions graded by LLM-as-judge

- Explanation questions
- Multiple choice with partial credit (using custom rubric)

## No Images/Figures Policy

We don't allow pictures or images in questions to avoid penalizing text-only agents. The rule is that figures must have a textual ground truth. No task should rely on visual interpretation alone.

Every figure should have a canonical textual representation that is sufficient to solve the task without seeing the image.

What to do instead:

- If a question depends on a figure, provide a verbose textual description of the figure or use structured diagram languages (e.g., [Mermaid](https://mermaid.js.org/))
- Convert visual information into tables, lists, or structured text descriptions
- Exclude questions that cannot be represented textually

## Data Format

The benchmark consists of exam questions stored in a structured format:

```
data/
├── raw/                      # Source exam.md files
│   └── example_course_2024_midterm/
│       └── exam.md
├── exams_metadata.json       # Exam-level metadata (generated)
├── questions.jsonl           # Question data (generated)
└── reference_materials/      # Cheatsheets and reference documents
    ├── raft_basics.md
    └── ...
```

### Exam Metadata Schema

`exams_metadata.json` contains exam-level information:

```json
{
  "exams": [
    {
      "exam_id": "example_course_2024_midterm",
      "test_paper_name": "Example Systems Course: 2024 Midterm Exam",
      "course": "Example Systems Course",
      "year": 2024,
      "score_total": 59,
      "num_questions": 10
    }
  ]
}
```

Required fields:

- `exam_id` (string): Unique exam identifier
- `test_paper_name` (string): Full exam name
- `course` (string): Course name
- `year` (integer): Year the exam was given
- `score_total` (number): Total points (must match sum of question points)
- `num_questions` (integer): Number of questions (must match actual count)

Optional fields:

- `institution` (string): University or institution name

### Question Schema

```json
{
  "input": "What state is a process in when it is waiting for I/O?",
  "target": "C",
  "choices": ["Running", "Ready", "Blocked", "Terminated"],
  "id": "example_course_2024_midterm_1",
  "metadata": {
    "exam_id": "example_course_2024_midterm",
    "problem_id": "1",
    "points": 5,
    "type": "ExactMatch",
    "tags": ["operating-systems", "processes"]
  }
}
```

Required fields:

- `input` (string): Question text in markdown format
- `target` (string): Correct answer
- `id` (string): Unique identifier
- `metadata`:
  - `exam_id` (string): Links to exam in exams_metadata.json
  - `problem_id` (string): Question identifier within exam (e.g., "1", "2.1", "4a")
  - `points` (integer): Points allocated to this question
  - `type` (string): Either "ExactMatch" or "Freeform"
  - `tags` (array): Topic tags (minimum 1, lowercase with hyphens)

Optional fields:

- `choices` (array): Answer choices for multiple choice/True-False questions. Required for ExactMatch questions with options. Target must be a letter (A, B, C, etc.) corresponding to the choice index.
- `metadata.reference_materials` (array): Paths to reference markdown files (e.g., `["reference_materials/raft_basics.md"]`)
- `metadata.llm_judge_instructions` (string): Custom grading rubric for Freeform questions

> If anything in this documentation or the example exam is unclear, please [open an issue](https://github.com/sys-intelligence/system-intelligence-benchmark/issues) with details about what needs clarification.
