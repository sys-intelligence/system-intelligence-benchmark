# Course Exam Benchmark

A benchmark for evaluating AI agents on systems course exam questions. This benchmark tests AI agents' ability to answer technical exam questions covering topics like operating systems, distributed systems, databases, and networking.

> Note: The infrastructure to run this benchmark is still work in progress. For now, we are focused on defining the data format and collecting exam questions.

## Scope: Standalone Questions Only

This benchmark is designed for standalone exam questions similar to traditional paper exams. Think of this as a closed-book exam with an optional cheatsheet where students solve questions using only pen and paper (no code execution, no file system access, no web browsing, or any other agent actions)

What's allowed:

- Plain text questions (single choice, True/False, short answer, etc.)
- Reference materials (markdown files serving as cheatsheets)

What's not allowed:

- Questions requiring code execution
- Questions requiring file system interaction
- Questions requiring web access or external tools
- Any form of agent execution beyond reading and answering
- Questions with images/figures (see below for details)

> We understand that different professors and universities use different terminology (e.g., "take-home exam," "assignments" instead of "labs"), but the line we draw is that the exam benchmark only includes plain text questions with optional reference markdown files. If a question requires any form of execution, environment setup, or interactive problem-solving, it belongs in the [Course Lab Benchmark](../courselab_bench/) instead, which offers more flexibility for coding tasks and agent interactions.

### No Images/Figures Policy

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
├── exams_metadata.json       # Exam-level metadata (generated)
├── questions.jsonl           # Question data (generated)
├── reference_materials/      # Cheatsheets and reference documents
│   ├── raft_basics.md
│   └── ...
└── example_course_2024_midterm/
    └── exam.md               # Exam in markdown format
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

### Question Types

ExactMatch: Questions with one correct answer, graded by exact string match

- Single choice (A/B/C/D)
- True/False

Freeform: Free-form text questions graded by LLM-as-judge

- Explanation questions
- Multiple choice with partial credit (using custom rubric)

### Question Schema

Each line in `questions.jsonl` is a JSON object:

```json
{
  "instance_id": 1,
  "exam_id": "example_course_2024_midterm",
  "problem_id": "1",
  "points": 5,
  "problem": "What state is a process in when it is waiting for I/O?...",
  "answer": "C",
  "type": "ExactMatch",
  "tags": ["operating-systems", "processes"]
}
```

Required fields:

- `instance_id` (integer): Globally unique identifier (incremental by 1)
- `exam_id` (string): Links to exam in exams_metadata.json
- `problem_id` (string): Question identifier within exam (e.g., "1", "2.1", "4a")
- `points` (integer): Points allocated to this question
- `problem` (string): Question text in markdown format
- `answer` (string): Correct answer
- `type` (string): Either "ExactMatch" or "Freeform"
- `tags` (array): Topic tags (minimum 1, lowercase with hyphens)

Optional fields:

- `reference_materials` (array): Paths to reference markdown files (e.g., `["reference_materials/raft_basics.md"]`)
- `llm_judge_instructions` (string): Custom grading rubric for Freeform questions

## Adding New Exams

Exams are written in markdown format and automatically converted to the JSON format using `prepare_dataset.py`.

### Markdown Format

See [data/example_course_2024_midterm/exam.md](data/example_course_2024_midterm/exam.md) for a complete example with comments explaining each question type.

Overview of the format:

- JSON block at the top for exam metadata
- Questions separated by `---`
- Question text in markdown
- JSON block for question metadata and answer
- Optional `comments` field for notes about the question

### Steps to Add an Exam

1. Create a new folder in `data/`: `data/your_exam_name/`
2. Create `exam.md` in that folder following the format (see [example_course_2024_midterm/exam.md](data/example_course_2024_midterm/exam.md))
3. (Optional) Add reference materials (`.md` files) to the same folder
4. Run the preparation script: `python prepare_dataset.py`

The script will automatically parse your markdown, assign incremental `instance_id` values, and generate `data/questions.jsonl` and `data/exams_metadata.json`. It will also copy any reference materials to `data/reference_materials/`.

> If anything in this documentation or the example exam is unclear, please [open an issue](https://github.com/sys-intelligence/system-intelligence-benchmark/issues) with details about what needs clarification.
