import base64
import json
from pathlib import Path
from inspect_ai.dataset import MemoryDataset, Sample
from inspect_ai.util import SandboxEnvironmentSpec


def load_dataset(
    task_dir: Path | str | None = None, task_ids: str | list[str] | None = None
):
    if task_dir is None:
        task_dir = Path(__file__).parent.parent / "data"
    else:
        task_dir = Path(task_dir)

    if isinstance(task_ids, str):
        task_ids = [task_ids]

    samples = []
    for config_path in task_dir.rglob("config.json"):
        if config_path.name == "courses.json":
            continue

        task_folder = config_path.parent
        with open(config_path) as f:
            config = json.load(f)

        instance_id = config["instance_id"]
        if task_ids and instance_id not in task_ids:
            continue

        task_description = (task_folder / "task.md").read_text()

        preprocess_path = task_folder / "preprocess.sh"
        setup_script = preprocess_path.read_text() if preprocess_path.exists() else None

        files = {}
        starter_dir = task_folder / "starter"
        if starter_dir.exists():
            for file_path in starter_dir.rglob("*"):
                if file_path.is_file():
                    relative_path = file_path.relative_to(starter_dir)
                    # Try to read as text, fallback to base64 data URI for binary files
                    try:
                        files[str(relative_path)] = file_path.read_text()
                    except UnicodeDecodeError:
                        # Handle binary files using base64 encoded data URI
                        binary_data = file_path.read_bytes()
                        b64_data = base64.b64encode(binary_data).decode('ascii')
                        files[str(relative_path)] = f"data:application/octet-stream;base64,{b64_data}"

        compose_file = task_folder / "compose.yaml"
        if not compose_file.exists():
            raise FileNotFoundError(
                f"compose.yaml required but not found in {task_folder}"
            )

        samples.append(
            Sample(
                id=instance_id,
                input=task_description,
                target="success",
                metadata={
                    "task_folder": str(task_folder.absolute()),
                    "course_id": config.get("course_id"),
                    "artifacts": config.get("artifacts", []),
                    "tags": config.get("tags", []),
                },
                sandbox=SandboxEnvironmentSpec(
                    type="docker",
                    config=str(compose_file.absolute()),
                ),
                setup=setup_script,
                files=files if files else None,
            )
        )

    if not samples:
        raise ValueError(f"No tasks found in {task_dir}")

    return MemoryDataset(samples=samples)


def load_courses_metadata(data_dir: Path | str | None = None):
    if data_dir is None:
        data_dir = Path(__file__).parent.parent / "data"
    else:
        data_dir = Path(data_dir)

    courses_path = data_dir / "courses.json"
    if courses_path.exists():
        with open(courses_path) as f:
            return json.load(f)
    return {"courses": []}
