import json
from pathlib import Path
import pytest

DATA_DIR = Path(__file__).parent.parent / "data"


def load_jsonl(file_path: Path) -> list[dict]:
    tasks = []
    with file_path.open("r") as f:
        for line in f:
            line = line.strip()
            if line:
                tasks.append(json.loads(line))
    return tasks


def load_json(file_path: Path) -> dict:
    with file_path.open("r") as f:
        return json.load(f)


class TestTasksSchema:
    def test_tasks_file_exists(self):
        assert (DATA_DIR / "tasks.jsonl").exists(), "tasks.jsonl not found"

    def test_tasks_valid_json(self):
        tasks = load_jsonl(DATA_DIR / "tasks.jsonl")
        assert len(tasks) > 0, "No tasks found in tasks.jsonl"

    def test_task_required_fields(self):
        tasks = load_jsonl(DATA_DIR / "tasks.jsonl")
        required_fields = [
            "instance_id",
            "course_id",
            "problem_statement",
            "docker_image",
            "test_command",
            "test_expected_substring",
        ]

        for task in tasks:
            for field in required_fields:
                assert (
                    field in task
                ), f"Task {task.get('instance_id', 'unknown')} missing field: {field}"

    def test_task_types(self):
        tasks = load_jsonl(DATA_DIR / "tasks.jsonl")

        for task in tasks:
            assert isinstance(task["instance_id"], str), "instance_id must be string"
            assert isinstance(task["course_id"], str), "course_id must be string"
            assert isinstance(task["problem_statement"], str), "problem_statement must be string"
            assert isinstance(task["docker_image"], str), "docker_image must be string"
            assert isinstance(task["test_command"], str), "test_command must be string"
            assert isinstance(
                task["test_expected_substring"], str
            ), "test_expected_substring must be string"

            # Optional fields
            if "repo_url" in task:
                assert isinstance(task["repo_url"], str), "repo_url must be string"
            if "base_commit" in task:
                assert isinstance(
                    task["base_commit"], (str, type(None))
                ), "base_commit must be string or null"
            if "install_commands" in task:
                assert isinstance(task["install_commands"], list), "install_commands must be list"
                for cmd in task["install_commands"]:
                    assert isinstance(cmd, str), "install_commands items must be strings"
            if "timeout_minutes" in task:
                assert isinstance(
                    task["timeout_minutes"], (int, float)
                ), "timeout_minutes must be number"
                assert task["timeout_minutes"] > 0, "timeout_minutes must be positive"
            if "tags" in task:
                assert isinstance(task["tags"], list), "tags must be list"
                for tag in task["tags"]:
                    assert isinstance(tag, str), "tags items must be strings"

    def test_instance_ids_unique(self):
        tasks = load_jsonl(DATA_DIR / "tasks.jsonl")
        instance_ids = [task["instance_id"] for task in tasks]
        assert len(instance_ids) == len(set(instance_ids)), "Duplicate instance_ids found"


class TestCoursesSchema:
    def test_courses_file_exists(self):
        assert (DATA_DIR / "courses.json").exists(), "courses.json not found"

    def test_courses_valid_json(self):
        data = load_json(DATA_DIR / "courses.json")
        assert "courses" in data, "courses.json must have 'courses' key"
        assert isinstance(data["courses"], list), "'courses' must be a list"

    def test_course_required_fields(self):
        data = load_json(DATA_DIR / "courses.json")
        required_fields = ["course_id", "name", "institution", "year"]

        for course in data["courses"]:
            for field in required_fields:
                assert (
                    field in course
                ), f"Course {course.get('course_id', 'unknown')} missing field: {field}"

    def test_course_types(self):
        data = load_json(DATA_DIR / "courses.json")

        for course in data["courses"]:
            assert isinstance(course["course_id"], str), "course_id must be string"
            assert isinstance(course["name"], str), "name must be string"
            assert isinstance(course["institution"], str), "institution must be string"
            assert isinstance(course["year"], int), "year must be integer"

            # Optional fields
            if "semester" in course:
                assert isinstance(course["semester"], str), "semester must be string"
            if "topics" in course:
                assert isinstance(course["topics"], list), "topics must be list"
                for topic in course["topics"]:
                    assert isinstance(topic, str), "topics items must be strings"
            if "course_url" in course:
                assert isinstance(course["course_url"], str), "course_url must be string"

    def test_course_ids_unique(self):
        data = load_json(DATA_DIR / "courses.json")
        course_ids = [course["course_id"] for course in data["courses"]]
        assert len(course_ids) == len(set(course_ids)), "Duplicate course_ids found"


class TestDataIntegrity:
    def test_task_course_refs_valid(self):
        tasks = load_jsonl(DATA_DIR / "tasks.jsonl")
        courses_data = load_json(DATA_DIR / "courses.json")
        course_ids = {course["course_id"] for course in courses_data["courses"]}

        for task in tasks:
            assert (
                task["course_id"] in course_ids
            ), f"Task {task['instance_id']} references non-existent course: {task['course_id']}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
