import time
from datetime import datetime
from typing import Any
from loguru import logger


def execute_task(task: dict[str, Any], agent: Any, env: Any) -> dict[str, Any]:
    instance_id = task["instance_id"]
    start_time = time.time()

    try:
        env.setup(task)
    except Exception as e:
        return {
            "instance_id": instance_id,
            "timestamp": datetime.now().isoformat(),
            "duration_seconds": time.time() - start_time,
            "error": f"Setup failed: {str(e)}",
            "trajectory": [],
            "agent_steps": 0,
            "agent_status": "setup_error",
            "model_cost": 0.0,
            "test_output": None,
            "test_exit_code": None,
        }

    try:
        agent_result = agent.run(task)
    except Exception as e:
        logger.error(f"Agent error: {e}")
        agent_result = {"messages": [], "cost": 0.0, "status": "agent_error", "steps": 0}

    test_command = task["test_command"]
    logger.info(f"\nRunning tests...")
    try:
        test_timeout = task.get("timeout_minutes", 30) * 60
        test_result = env.execute(test_command, timeout=test_timeout)
    except Exception as e:
        logger.error(f"Test error: {e}")
        test_result = {"output": f"[ERROR: {e}]", "returncode": -1}

    duration = time.time() - start_time

    result = {
        "instance_id": instance_id,
        "timestamp": datetime.now().isoformat(),
        "duration_seconds": round(duration, 2),
        "trajectory": agent_result.get("messages", []),
        "agent_steps": agent_result.get("steps", 0),
        "agent_status": agent_result.get("status", "unknown"),
        "model_cost": agent_result.get("cost", 0.0),
        "test_output": test_result.get("output"),
        "test_exit_code": test_result.get("returncode"),
    }

    status_symbol = "✓" if test_result.get("returncode") == 0 else "✗"
    logger.info(
        f"{status_symbol} Completed in {duration:.1f}s "
        f"({agent_result.get('steps', 0)} steps, ${result['model_cost']:.4f})"
    )

    return result
