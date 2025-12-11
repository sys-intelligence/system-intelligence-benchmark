from collections import defaultdict
from typing import Any


def evaluate_task(result: dict[str, Any]) -> bool:
    return result.get("test_exit_code") == 0


def compute_summary(results: list[dict[str, Any]]) -> dict[str, Any]:
    if not results:
        return {"total": 0, "passed": 0, "success_rate": 0.0}

    total = len(results)
    passed = sum(1 for r in results if r.get("passed", False))

    costs = [r["model_cost"] for r in results if "model_cost" in r]
    durations = [r["duration_seconds"] for r in results if "duration_seconds" in r]

    summary = {
        "total": total,
        "passed": passed,
        "success_rate": passed / total if total > 0 else 0.0,
        "total_cost": round(sum(costs), 4) if costs else 0.0,
        "avg_duration": round(sum(durations) / len(durations), 2) if durations else 0.0,
    }

    by_course = defaultdict(lambda: {"total": 0, "passed": 0})
    for result in results:
        course_id = result.get("course_id", "unknown")
        by_course[course_id]["total"] += 1
        if result.get("passed", False):
            by_course[course_id]["passed"] += 1

    summary["by_course"] = {
        course_id: {
            **stats,
            "success_rate": stats["passed"] / stats["total"] if stats["total"] > 0 else 0.0,
        }
        for course_id, stats in sorted(by_course.items())
    }

    return summary
