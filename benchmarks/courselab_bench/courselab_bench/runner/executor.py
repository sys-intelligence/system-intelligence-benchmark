import time
from datetime import datetime
from typing import Any
from loguru import logger


def _run_evaluate_script(env: Any, evaluate_script: str, timeout: int) -> dict[str, Any]:
    script_path = f"{env.work_dir}/evaluate.sh"
    env.execute(f"cat > {script_path} << 'EVALUATE_EOF'\n{evaluate_script}\nEVALUATE_EOF")
    env.execute(f"chmod +x {script_path}")
    result = env.execute(f"cd {env.work_dir} && bash {script_path}", timeout=timeout)
    return result


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

    logger.info(f"\nRunning evaluation...")

    # Retry evaluation up to 3 times to handle flaky tests
    max_retries = 3
    test_result = None
    for attempt in range(1, max_retries + 1):
        try:
            if attempt > 1:
                logger.info(f"Retry attempt {attempt}/{max_retries}...")
            test_timeout = task.get("timeout_minutes", 30) * 60
            test_result = _run_evaluate_script(env, task["evaluate_script"], test_timeout)

            if test_result.get("returncode") == 0:
                if attempt > 1:
                    logger.info(f"Evaluation passed on attempt {attempt}")
                break

            if attempt < max_retries:
                logger.warning(f"Evaluation failed on attempt {attempt}, retrying...")
        except Exception as e:
            logger.error(f"Evaluation error on attempt {attempt}: {e}")
            test_result = {"output": f"[ERROR: {e}]", "returncode": -1}
            if attempt < max_retries:
                logger.warning(f"Retrying after error...")
    if test_result is None:
        test_result = {"output": "[ERROR: No test result]", "returncode": -1}

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
