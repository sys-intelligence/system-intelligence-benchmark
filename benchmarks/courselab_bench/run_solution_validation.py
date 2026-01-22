#!/usr/bin/env python3

import json
from pathlib import Path
from inspect_ai import eval
from courselab import courselab, solution_agent

TASK_IDS = None


def get_tasks_with_solutions(data_dir: Path | None = None) -> list[str]:
    if data_dir is None:
        data_dir = Path(__file__).parent / "data"

    tasks = []
    for config_path in data_dir.rglob("config.json"):
        if config_path.name == "courses.json":
            continue

        with open(config_path) as f:
            config = json.load(f)

        if (config_path.parent / "sol.sh").exists():
            tasks.append(config["instance_id"])

    return tasks


if __name__ == "__main__":
    if TASK_IDS:
        task_ids = [TASK_IDS] if isinstance(TASK_IDS, str) else TASK_IDS
        available = get_tasks_with_solutions()
        task_ids = [t for t in task_ids if t in available]
    else:
        task_ids = get_tasks_with_solutions()

    eval(
        tasks=courselab(task_ids=task_ids, agent=solution_agent(), max_turns=10),
        model=None,
        limit=None,
    )
