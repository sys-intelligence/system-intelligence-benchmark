import json
from pathlib import Path
import pytest

DATA_DIR = Path(__file__).parent.parent / "data"


def get_task_folders(data_dir: Path) -> list[Path]:
    task_folders = []
    for item in data_dir.iterdir():
        if not item.is_dir():
            continue
        if (item / "config.json").exists():
            task_folders.append(item)
        else:
            for task_dir in item.iterdir():
                if task_dir.is_dir() and (task_dir / "config.json").exists():
                    task_folders.append(task_dir)
    return task_folders


class TestTaskStructure:
    def test_data_dir_exists(self):
        assert DATA_DIR.exists(), f"Data directory not found: {DATA_DIR}"

    def test_tasks_found(self):
        task_folders = get_task_folders(DATA_DIR)
        assert len(task_folders) > 0, "No tasks found in data directory"

    def test_required_files_exist(self):
        task_folders = get_task_folders(DATA_DIR)
        required_files = ["config.json", "task.md", "preprocess.sh", "evaluate.sh"]

        for task_folder in task_folders:
            for filename in required_files:
                file_path = task_folder / filename
                assert file_path.exists(), f"{task_folder.name} missing {filename}"

    def test_config_valid_json(self):
        task_folders = get_task_folders(DATA_DIR)

        for task_folder in task_folders:
            config_path = task_folder / "config.json"
            with config_path.open("r") as f:
                config = json.load(f)
            assert isinstance(config, dict), f"{task_folder.name}: config.json must be object"

    def test_config_required_fields(self):
        task_folders = get_task_folders(DATA_DIR)
        required_fields = ["instance_id", "course_id", "docker_image"]

        for task_folder in task_folders:
            config_path = task_folder / "config.json"
            with config_path.open("r") as f:
                config = json.load(f)

            for field in required_fields:
                assert field in config, f"{task_folder.name}: missing {field}"
                assert isinstance(config[field], str), f"{task_folder.name}: {field} must be string"

    def test_config_optional_fields(self):
        task_folders = get_task_folders(DATA_DIR)

        for task_folder in task_folders:
            config_path = task_folder / "config.json"
            with config_path.open("r") as f:
                config = json.load(f)

            if "timeout_minutes" in config:
                assert isinstance(config["timeout_minutes"], (int, float))
                assert config["timeout_minutes"] > 0

            if "tags" in config:
                assert isinstance(config["tags"], list)
                for tag in config["tags"]:
                    assert isinstance(tag, str)

            if "repo_url" in config:
                assert isinstance(config["repo_url"], (str, type(None)))

            if "base_commit" in config:
                assert isinstance(config["base_commit"], (str, type(None)))

            if "starter_files" in config:
                assert isinstance(config["starter_files"], list)
                for item in config["starter_files"]:
                    assert isinstance(item, dict)
                    assert "src" in item
                    assert "dest" in item
                    assert isinstance(item["src"], str)
                    assert isinstance(item["dest"], str)

            if "output_files" in config:
                assert isinstance(config["output_files"], list)
                for item in config["output_files"]:
                    assert isinstance(item, dict)
                    assert "src" in item
                    assert "dest" in item
                    assert isinstance(item["src"], str)
                    assert isinstance(item["dest"], str)

    def test_scripts_executable(self):
        task_folders = get_task_folders(DATA_DIR)
        script_files = ["preprocess.sh", "evaluate.sh"]

        for task_folder in task_folders:
            for script in script_files:
                script_path = task_folder / script
                assert script_path.exists()

    def test_instance_ids_unique(self):
        task_folders = get_task_folders(DATA_DIR)
        instance_ids = []

        for task_folder in task_folders:
            config_path = task_folder / "config.json"
            with config_path.open("r") as f:
                config = json.load(f)
            instance_ids.append(config["instance_id"])

        assert len(instance_ids) == len(set(instance_ids)), "Duplicate instance_ids found"

    def test_starter_files_exist(self):
        task_folders = get_task_folders(DATA_DIR)
        for task_folder in task_folders:
            config_path = task_folder / "config.json"
            with config_path.open("r") as f:
                config = json.load(f)

            if "starter_files" in config:
                for item in config["starter_files"]:
                    src_file = task_folder / "starter_files" / item["src"]
                    assert (
                        src_file.exists()
                    ), f"{task_folder.name}: starter file not found: {item['src']}"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
