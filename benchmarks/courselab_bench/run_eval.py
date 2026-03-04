#!/usr/bin/env python3

import argparse
import os
from pathlib import Path

from inspect_ai import eval

from courselab import courselab


def parse_args():
    parser = argparse.ArgumentParser(description='Run CourseLab benchmark via inspect_ai')
    parser.add_argument('--model', default='anthropic/claude-haiku-4-5', help='Model name for evaluation')
    parser.add_argument('--max-turns', type=int, default=100, help='Max turns per task')
    parser.add_argument('--limit', type=int, default=None, help='Optional limit on evaluated samples')
    parser.add_argument(
        '--task-ids',
        default='distributed_systems__echo_server',
        help='Comma-separated task IDs',
    )
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

    eval(
        tasks=courselab(task_ids=split_csv(args.task_ids), max_turns=args.max_turns),
        model=args.model,
        limit=args.limit,
    )
