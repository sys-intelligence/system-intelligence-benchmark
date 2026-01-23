#!/usr/bin/env python3

from inspect_ai import eval

from courseexam.courseexam import courseexam

# Configuration - modify these constants as needed
MODELS = [
    "anthropic/claude-sonnet-4-5",
    "anthropic/claude-haiku-4-5"
]
JUDGE_MODEL = "anthropic/claude-sonnet-4-5"
LIMIT = None
EXAM_IDS = None
QUESTION_TYPES = None
TAGS = None

if __name__ == "__main__":
    for model in MODELS:
        task = courseexam(
            exam_ids=EXAM_IDS,
            question_types=QUESTION_TYPES,
            tags=TAGS,
            judge_model=JUDGE_MODEL,
        )

        eval(tasks=task, model=model, limit=LIMIT)
