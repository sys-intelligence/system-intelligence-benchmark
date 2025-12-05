from collections import defaultdict
from typing import Any


def compute_summary(evaluations: list[dict[str, Any]]) -> dict[str, Any]:
    if not evaluations:
        return {
            "overall": {
                "total": 0,
                "passed": 0,
                "failed": 0,
                "success_rate": 0.0,
                "avg_cost": 0.0,
                "avg_duration": 0.0,
                "avg_steps": 0.0,
            },
            "by_course": [],
        }

    total = len(evaluations)
    passed = sum(1 for e in evaluations if e["passed"])
    failed = total - passed
    success_rate = passed / total if total > 0 else 0.0

    # Compute averages only for successful tasks
    costs = [e.get("model_cost", 0) for e in evaluations if e.get("model_cost") is not None]
    durations = [
        e.get("duration_seconds", 0) for e in evaluations if e.get("duration_seconds") is not None
    ]
    steps = [e.get("agent_steps", 0) for e in evaluations if e.get("agent_steps") is not None]

    avg_cost = sum(costs) / len(costs) if costs else 0.0
    avg_duration = sum(durations) / len(durations) if durations else 0.0
    avg_steps = sum(steps) / len(steps) if steps else 0.0

    overall = {
        "total": total,
        "passed": passed,
        "failed": failed,
        "success_rate": success_rate,
        "avg_cost": round(avg_cost, 4),
        "avg_duration": round(avg_duration, 2),
        "avg_steps": round(avg_steps, 1),
    }

    # Group by course
    by_course = defaultdict(
        lambda: {"total": 0, "passed": 0, "costs": [], "durations": [], "steps": []}
    )
    for eval_dict in evaluations:
        course_id = eval_dict.get("course_id", "unknown")
        by_course[course_id]["total"] += 1
        if eval_dict["passed"]:
            by_course[course_id]["passed"] += 1
        if eval_dict.get("model_cost"):
            by_course[course_id]["costs"].append(eval_dict["model_cost"])
        if eval_dict.get("duration_seconds"):
            by_course[course_id]["durations"].append(eval_dict["duration_seconds"])
        if eval_dict.get("agent_steps"):
            by_course[course_id]["steps"].append(eval_dict["agent_steps"])

    by_course_list = []
    for course_id, stats in sorted(by_course.items()):
        by_course_list.append(
            {
                "course_id": course_id,
                "total": stats["total"],
                "passed": stats["passed"],
                "failed": stats["total"] - stats["passed"],
                "success_rate": stats["passed"] / stats["total"] if stats["total"] > 0 else 0.0,
                "avg_cost": (
                    round(sum(stats["costs"]) / len(stats["costs"]), 4) if stats["costs"] else 0.0
                ),
                "avg_duration": (
                    round(sum(stats["durations"]) / len(stats["durations"]), 2)
                    if stats["durations"]
                    else 0.0
                ),
                "avg_steps": (
                    round(sum(stats["steps"]) / len(stats["steps"]), 1) if stats["steps"] else 0.0
                ),
            }
        )

    return {"overall": overall, "by_course": by_course_list}
