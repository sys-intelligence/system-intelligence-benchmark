from pathlib import Path
from inspect_ai import Task, task
from inspect_ai.agent import Agent

from courselab.dataset import load_dataset, load_courses_metadata
from courselab.scorer import lab_scorer
from courselab.solver import lab_agent


@task
def courselab(
    task_dir: Path | str | None = None,
    task_ids: str | list[str] | None = None,
    agent: Agent | None = None,
    max_turns: int = 30,
) -> Task:
    dataset = load_dataset(task_dir=task_dir, task_ids=task_ids)
    metadata = load_courses_metadata(data_dir=Path(task_dir) if task_dir else None)

    return Task(
        dataset=dataset,
        solver=agent or lab_agent(),
        scorer=lab_scorer(),
        max_messages=max_turns,
        metadata={
            "num_courses": len(metadata["courses"]),
            "courses": metadata["courses"],
        },
    )
