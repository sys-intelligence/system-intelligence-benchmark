#!/usr/bin/env python3
from inspect_ai import eval
from courselab import courselab

MODELS = [
    "anthropic/claude-haiku-4-5",
    "anthropic/claude-sonnet-4-5",
]
MAX_TURNS = 100
LIMIT = None
TASK_IDS = [
    "cmu_15-213__data_lab",
    "mit_6_5840_2024__kvraft_4a",
    "mit_6_5840_2024__kvraft_4b",
    "mit_6_5840_2024__kvsrv",
    "mit_6_5840_2024__kvsrv_2b",
    "mit_6_5840_2024__mapreduce",
    "mit_6_5840_2024__raft_3a",
    "mit_6_5840_2024__raft_3b",
    "mit_6_5840_2024__raft_3c",
    "mit_6_5840_2024__raft_3d",
    "mit_6_5840_2024__shardkv_5a",
    "mit_6_5840_2024__shardkv_5b",
]

if __name__ == "__main__":
    for model in MODELS:
        eval(
            tasks=courselab(task_ids=TASK_IDS, max_turns=MAX_TURNS),
            model=model,
            limit=LIMIT,
        )
