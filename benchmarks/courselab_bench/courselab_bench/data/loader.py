import json
from pathlib import Path
from typing import Any
from loguru import logger


def load_tasks(file_path: str | Path) -> list[dict[str, Any]]:
    file_path = Path(file_path)

    if not file_path.exists():
        raise FileNotFoundError(f"Tasks file not found: {file_path}")

    tasks = []
    with file_path.open("r", encoding="utf-8") as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue

            try:
                task = json.loads(line)
                tasks.append(task)
            except json.JSONDecodeError as e:
                logger.warning(f"Skipping invalid JSON on line {line_num}: {e}")
                continue

    return tasks


def load_courses(file_path: str | Path) -> dict[str, dict[str, Any]]:
    file_path = Path(file_path)

    if not file_path.exists():
        raise FileNotFoundError(f"Courses file not found: {file_path}")

    logger.info(f"Loading courses from: {file_path}")

    with file_path.open("r", encoding="utf-8") as f:
        data = json.load(f)

    courses = {}
    for course in data.get("courses", []):
        course_id = course.get("course_id")
        if course_id:
            courses[course_id] = course
        else:
            logger.warning(f"Course missing course_id: {course}")

    logger.info(f"Loaded {len(courses)} courses")
    return courses


def filter_tasks(tasks: list[dict[str, Any]], filter_spec: dict[str, Any]) -> list[dict[str, Any]]:
    filtered = tasks

    instance_ids = filter_spec.get("instance_ids")
    if instance_ids is not None:
        filtered = [t for t in filtered if t.get("instance_id") in instance_ids]
        logger.debug(f"Filtered by instance_ids: {len(filtered)} tasks remain")

    course_ids = filter_spec.get("course_ids")
    if course_ids is not None:
        filtered = [t for t in filtered if t.get("course_id") in course_ids]
        logger.debug(f"Filtered by course_ids: {len(filtered)} tasks remain")

    # Filter by tags (task must have at least one matching tag)
    tags = filter_spec.get("tags")
    if tags is not None:
        filtered = [t for t in filtered if any(tag in t.get("tags", []) for tag in tags)]
        logger.debug(f"Filtered by tags: {len(filtered)} tasks remain")

    logger.info(f"Filtered tasks: {len(tasks)} → {len(filtered)}")
    return filtered
