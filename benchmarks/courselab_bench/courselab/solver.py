from textwrap import dedent
from inspect_ai.agent import Agent, agent, react
from inspect_ai.tool import bash


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
