#!/usr/bin/env python3
from inspect_ai import eval
from courselab import courselab

MODEL = "anthropic/claude-haiku-4-5"
MAX_TURNS = 100
LIMIT = None
TASK_IDS = "distributed_systems__echo_server"

if __name__ == "__main__":
    eval(
        tasks=courselab(task_ids=TASK_IDS, max_turns=MAX_TURNS),
        model=MODEL,
        limit=LIMIT,
    )
