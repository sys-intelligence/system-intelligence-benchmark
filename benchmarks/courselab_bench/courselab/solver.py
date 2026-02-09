from pathlib import Path
from textwrap import dedent
from typing import Any
from inspect_ai.agent import Agent, agent, react, as_solver
from inspect_ai.solver import Solver, TaskState, solver
from inspect_ai.tool import bash
from inspect_ai.util import sandbox
from inspect_ai.model import ChatMessageUser, ChatMessageAssistant


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
def multi_round_solver(base_agent: Agent) -> Solver:
    """Solver that handles multi-round tasks with independent conversation contexts."""
    # Convert agent to solver
    agent_solver = as_solver(base_agent)
    
    async def solve(state: TaskState, generate: Any) -> TaskState:
        # Check if this is a multi-round task
        if not state.metadata.get("multi_round", False):
            # Not a multi-round task, use the base agent normally
            return await agent_solver(state, generate)
        
        # Multi-round task: run each round with independent conversation context
        num_rounds = state.metadata["num_rounds"]
        round_tasks = state.metadata["round_tasks"]
        
        # Store original messages
        original_messages = state.messages.copy()
        
        # Run each round with independent conversation context
        for round_num in range(1, num_rounds + 1):
            # Reset messages for this round (independent context)
            # Note: state.input is read-only, so we only reset messages
            state.messages = [ChatMessageUser(content=round_tasks[round_num])]
            state.metadata["current_round"] = round_num
            state.metadata["total_rounds"] = num_rounds
            
            # Run the agent for this round
            state = await agent_solver(state, generate)
            
            # Store round results in metadata
            if "round_results" not in state.metadata:
                state.metadata["round_results"] = {}
            state.metadata["round_results"][round_num] = {
                "completed": True,
            }
        
        return state

    return solve


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
