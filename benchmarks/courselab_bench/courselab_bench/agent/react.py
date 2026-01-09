import re
import subprocess
import time
from typing import Any
from loguru import logger


class AgentException(Exception):
    pass


class FormatError(AgentException):
    pass


class TimeoutError(AgentException):
    pass


class LimitReached(AgentException):
    pass


class TaskCompleted(AgentException):
    pass


class REACTAgent:
    def __init__(self, model: Any, env: Any, config: dict[str, Any]):
        self.model = model
        self.env = env
        self.config = config
        self.messages: list[dict[str, Any]] = []

    def run(self, task: dict[str, Any]) -> dict[str, Any]:
        self.messages = []
        self.add_message("system", self._system_prompt())
        self.add_message("user", self._task_prompt(task))

        try:
            while True:
                self.step()
        except LimitReached as e:
            logger.info(f"Limit reached: {e}")
            return self._finalize("limit_reached", str(e))
        except TaskCompleted as e:
            logger.info("Task completed successfully")
            return self._finalize("completed", str(e))
        except Exception as e:
            logger.error(f"Unexpected error: {e}")
            return self._finalize("error", str(e))

    def step(self):
        response = self.query()
        try:
            action = self.parse_action(response)
        except FormatError as e:
            # Format errors are recoverable - give the agent another chance
            logger.warning(f"Format error: {e}")
            self.add_message("user", str(e))
            return

        try:
            output = self.execute_action(action)
        except TimeoutError as e:
            # Timeout errors are recoverable - give the agent another chance
            logger.warning(f"Timeout: {e}")
            self.add_message("user", str(e))
            return

        self.add_observation(output)

    def query(self) -> dict[str, Any]:
        max_steps = self.config.get("max_steps", 50)
        max_cost = self.config.get("max_cost", 5.0)  # Default $5 cost limit

        num_steps = len([m for m in self.messages if m["role"] == "assistant"])
        if num_steps >= max_steps:
            raise LimitReached(f"Step limit reached: {num_steps}/{max_steps}")

        stats = self.model.get_stats()
        if stats["cost"] >= max_cost:
            raise LimitReached(f"Cost limit reached: ${stats['cost']:.4f} >= ${max_cost}")

        logger.debug(f"Querying model (step {num_steps + 1}/{max_steps})")
        try:
            response = self.model.query(self.messages)
            self.add_message("assistant", response["content"])
            return response
        except Exception as e:
            logger.error(f"Model query failed: {e}")
            raise

    def parse_action(self, response: dict[str, Any]) -> str:
        content = response["content"]
        action = self._parse_action(content)

        if action is None:
            raise FormatError(
                "Error: Please provide exactly ONE bash command in triple backticks (```bash ... ```)."
            )

        return action

    def execute_action(self, action: str) -> dict[str, Any]:
        if "TASK_COMPLETE" in action:
            raise TaskCompleted("Agent marked task as complete")

        display_action = (
            action if len(action) <= 200 else action[:200] + "..."
        )  # Truncate long commands
        logger.info(f"→ Executing: {display_action}")
        try:
            output = self.env.execute(action)
            output["action"] = action

            if output.get("returncode") == 0:
                logger.info(f"✓ Command succeeded (exit code 0)")
            else:
                logger.warning(f"✗ Command failed (exit code {output.get('returncode')})")

            return output
        except subprocess.TimeoutExpired as e:
            partial_output = e.stdout.decode("utf-8", errors="replace") if e.stdout else ""
            raise TimeoutError(
                f"Command timed out after {e.timeout}s.\n"
                f"Command: {action}\n"
                f"Partial output: {partial_output[:500]}"
            )
        except Exception as e:
            logger.error(f"Execution failed: {e}")
            return {"action": action, "output": f"[ERROR: {e}]", "returncode": 1}

    def add_observation(self, output: dict[str, Any]):
        observation = self._format_observation(output)
        self.add_message("user", observation)

    def add_message(self, role: str, content: str):
        self.messages.append({"role": role, "content": content, "timestamp": time.time()})

    def _finalize(self, status: str, message: str) -> dict[str, Any]:
        num_steps = len([m for m in self.messages if m["role"] == "assistant"])

        return {
            "messages": self.messages,
            "cost": self.model.get_stats()["cost"],
            "status": status,
            "steps": num_steps,
        }

    # For now, prompts are not configurable externally
    def _system_prompt(self) -> str:
        return """You are a systems programming assistant that solves tasks using bash commands.

Rules:
- Provide EXACTLY ONE bash command per response
- Format your commands in triple backticks: ```bash
command here
```
- After each command, wait for the output before proceeding
- When you have completed the task, run: echo "TASK_COMPLETE"
- Be concise and focused on solving the task

Important: Focus on the Current Lab
- You are working on a specific lab assignment from a course sequence
- Avoid getting distracted by code from earlier labs in the course sequence
- The task description clearly states which files you should modify"""

    def _task_prompt(self, task: dict[str, Any]) -> str:
        return f"""# Task: {task['instance_id']}

{task['problem_statement']}

## Instructions
Solve this task step by step using bash commands. Provide one command at a time and wait for the output.
When you are done, echo "TASK_COMPLETE" to signal completion."""

    def _parse_action(self, content: str) -> str | None:
        # Match ```bash ... ``` blocks
        pattern = r"```bash\s*\n(.*?)```"
        matches = re.findall(pattern, content, re.DOTALL)

        if matches:
            return matches[0].strip()

        return None

    def _format_observation(self, output: dict[str, Any]) -> str:
        returncode = output.get("returncode", -1)
        output_text = output.get("output", "")

        max_output_len = 5000
        if len(output_text) > max_output_len:
            output_text = (
                output_text[:max_output_len]
                + f"\n... (truncated {len(output_text) - max_output_len} chars)"
            )

        return f"""Exit code: {returncode}

Output:
{output_text}"""
