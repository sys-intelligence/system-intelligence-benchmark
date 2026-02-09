from importlib.metadata import version
from pathlib import Path
from typing import Any

from inspect_ai import Task, task
from inspect_ai.agent import Agent, as_solver
from inspect_ai.solver import Solver, TaskState, solver

from courselab.dataset import load_dataset, load_courses_metadata
from courselab.scorer import lab_scorer
from courselab.solver import lab_agent, multi_round_solver


@solver
def adaptive_solver(base_agent: Agent) -> Solver:
    """Solver that adapts to single-round or multi-round tasks."""
    # Convert agent to solver
    agent_solver = as_solver(base_agent)
    
    async def solve(state: TaskState, generate: Any) -> TaskState:
        # Check if this is a multi-round task
        if state.metadata.get("multi_round", False):
            # Use multi-round solver
            multi_round = multi_round_solver(base_agent)
            return await multi_round(state, generate)
        else:
            # Use base agent normally
            return await agent_solver(state, generate)
    
    return solve


@task
def courselab(
    task_dir: Path | str | None = None,
    task_ids: str | list[str] | None = None,
    agent: Agent | Solver | None = None,
    max_turns: int = 30,
) -> Task:
    dataset = load_dataset(task_dir=task_dir, task_ids=task_ids)
    metadata = load_courses_metadata(data_dir=Path(task_dir) if task_dir else None)

    # Use adaptive solver that handles both single and multi-round tasks
    # If a custom solver is provided, use it directly (solution_agent is not affected)
    if agent is not None and isinstance(agent, Solver):
        solver_to_use = agent
    else:
        # Use default agent or provided agent, wrapped with adaptive solver
        base_agent = agent if isinstance(agent, Agent) else lab_agent()
        solver_to_use = adaptive_solver(base_agent)

    return Task(
        dataset=dataset,
        solver=solver_to_use,
        scorer=lab_scorer(),
        max_messages=max_turns,
        metadata={
            "num_courses": len(metadata["courses"]),
            "courses": metadata["courses"],
        },
        name="courselab",
        version=version("courselab-bench"),
    )
