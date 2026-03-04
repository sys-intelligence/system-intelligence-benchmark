#!/usr/bin/env python3

import argparse
import os
from pathlib import Path

from inspect_ai import eval

from courseexam.courseexam import courseexam


def parse_args():
    parser = argparse.ArgumentParser(description='Run CourseExam benchmark via inspect_ai')
    parser.add_argument('--model', default='anthropic/claude-haiku-4-5', help='Model name for evaluation')
    parser.add_argument('--judge-model', default='anthropic/claude-haiku-4-5', help='Judge model name')
    parser.add_argument('--limit', type=int, default=None, help='Optional limit on evaluated samples')
    parser.add_argument(
        '--exam-ids',
        default=None,
        help='Comma-separated exam IDs to include, e.g. "cs61a_fa24,cs186_sp24"',
    )
    parser.add_argument('--question-types', default=None, help='Comma-separated question types to include')
    parser.add_argument('--tags', default=None, help='Comma-separated tags to include')
    return parser.parse_args()


def split_csv(value):
    if value is None or value.strip() == '':
        return None
    return [v.strip() for v in value.split(',') if v.strip()]


if __name__ == "__main__":
    args = parse_args()
    bench_root = Path(__file__).resolve().parent
    os.environ.setdefault('XDG_DATA_HOME', str(bench_root / '.xdg-data'))
    os.environ.setdefault('XDG_CACHE_HOME', str(bench_root / '.xdg-cache'))

    task = courseexam(
        exam_ids=split_csv(args.exam_ids),
        question_types=split_csv(args.question_types),
        tags=split_csv(args.tags),
        judge_model=args.judge_model,
    )

    eval(tasks=task, model=args.model, limit=args.limit)
