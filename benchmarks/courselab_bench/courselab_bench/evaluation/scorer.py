import json
from pathlib import Path
from typing import Any
from loguru import logger

from courselab_bench.data.loader import load_tasks
from courselab_bench.evaluation.metrics import compute_summary


def evaluate_result(result: dict[str, Any], task: dict[str, Any]) -> dict[str, Any]:
    instance_id = result["instance_id"]
    test_output = result.get("test_output", "")
    test_exit_code = result.get("test_exit_code")
    expected_substring = task.get("test_expected_substring", "")

    if test_output is None:
        return {
            "instance_id": instance_id,
            "passed": False,
            "score": 0.0,
            "reason": "Test did not run (output is None)",
            "expected": expected_substring,
            "actual_output": None,
        }

    # Check if expected substring is in output
    passed = expected_substring in test_output

    # Also consider test exit code (if 0, that's good)
    if test_exit_code is not None and test_exit_code != 0 and passed:
        logger.warning(f"{instance_id}: Test output matches but exit code is {test_exit_code}")

    reason = f"Expected '{expected_substring}' {'found' if passed else 'not found'} in test output"

    return {
        "instance_id": instance_id,
        "passed": passed,
        "score": 1.0 if passed else 0.0,
        "reason": reason,
        "expected": expected_substring,
        "test_exit_code": test_exit_code,
        "actual_output": test_output[:500] if test_output else None,  # Truncate for storage
    }


def evaluate_results(results_dir: Path | str, tasks_file: Path | str) -> dict[str, Any]:
    results_dir = Path(results_dir)
    tasks_file = Path(tasks_file)

    tasks = load_tasks(tasks_file)
    tasks_by_id = {task["instance_id"]: task for task in tasks}

    # Find all result JSON files
    excluded_files = ["evaluations.json", "summary.json", "config.json", "results_summary.json"]
    result_files = [f for f in results_dir.glob("*.json") if f.name not in excluded_files]

    if not result_files:
        logger.warning("No result files found")
        return {"overall": {"total": 0, "passed": 0, "failed": 0, "success_rate": 0.0}}

    evaluations = []
    for result_file in sorted(result_files):
        with result_file.open("r") as f:
            result = json.load(f)

        instance_id = result["instance_id"]
        if instance_id not in tasks_by_id:
            logger.warning(f"Task not found for {instance_id}, skipping")
            continue

        task = tasks_by_id[instance_id]
        evaluation = evaluate_result(result, task)
        evaluation["duration_seconds"] = result.get("duration_seconds")
        evaluation["agent_steps"] = result.get("agent_steps")
        evaluation["agent_status"] = result.get("agent_status")
        evaluation["model_cost"] = result.get("model_cost")
        evaluation["course_id"] = task.get("course_id")
        evaluation["tags"] = task.get("tags", [])
        evaluations.append(evaluation)

    evaluations_file = results_dir / "evaluations.json"
    with evaluations_file.open("w") as f:
        json.dump(evaluations, f, indent=2)

    summary = compute_summary(evaluations)
    summary_file = results_dir / "summary.json"
    with summary_file.open("w") as f:
        json.dump(summary, f, indent=2)

    overall = summary["overall"]
    logger.info(
        f"Results: {overall['passed']}/{overall['total']} passed ({overall['success_rate']:.1%})"
    )

    return summary
