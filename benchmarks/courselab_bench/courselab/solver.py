from pathlib import Path
from textwrap import dedent
from typing import Any
from inspect_ai.agent import Agent, agent, react
from inspect_ai.solver import Solver, TaskState, solver
from inspect_ai.tool import bash
from inspect_ai.util import sandbox


@agent
def lab_agent() -> Agent:
    return react(
        description="Student completing a systems programming lab assignment",
        prompt=dedent(
            """
            You are a student working on a lab assignment for a systems programming course.

            Use the bash tool to complete the assignment.
        """
        ),
        tools=[bash()],
        submit=False,
    )


@solver
def solution_agent() -> Solver:
    async def solve(state: TaskState, generate: Any) -> TaskState:
        task_folder = Path(state.metadata["task_folder"])
        sol_path = task_folder / "sol.sh"

        if sol_path.exists():
            sol_script = sol_path.read_text()
            result = await sandbox().exec(["bash", "-c", sol_script])

            from inspect_ai.model import ChatMessageAssistant
            state.messages.append(
                ChatMessageAssistant(
                    content=f"Executed solution script:\nSTDOUT: {result.stdout}\nSTDERR: {result.stderr}\nExit code: {result.returncode}"
                )
            )

        return state

    return solve
