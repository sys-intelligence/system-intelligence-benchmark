#!/usr/bin/env python3
import json
import sys
from pathlib import Path
from loguru import logger


def load_task_from_folder(task_folder: Path) -> dict:
    config_path = task_folder / "config.json"
    task_md_path = task_folder / "task.md"
    preprocess_path = task_folder / "preprocess.sh"
    evaluate_path = task_folder / "evaluate.sh"

    required_files = [config_path, task_md_path, preprocess_path, evaluate_path]
    for file_path in required_files:
        if not file_path.exists():
            raise FileNotFoundError(f"{file_path.name} not found in {task_folder}")

    with config_path.open("r") as f:
        config = json.load(f)

    with task_md_path.open("r") as f:
        problem_statement = f.read()

    with preprocess_path.open("r") as f:
        preprocess_script = f.read()

    with evaluate_path.open("r") as f:
        evaluate_script = f.read()

    task_data = {
        "instance_id": config["instance_id"],
        "course_id": config["course_id"],
        "problem_statement": problem_statement,
        "docker_image": config["docker_image"],
        "timeout_minutes": config.get("timeout_minutes", 30),
        "tags": config.get("tags", []),
        "preprocess_script": preprocess_script,
        "evaluate_script": evaluate_script,
        "repo_url": config.get("repo_url"),
        "base_commit": config.get("base_commit"),
        "task_folder": str(task_folder.resolve()),
    }

    if "starter_files" in config:
        task_data["starter_files"] = config["starter_files"]
    if "output_files" in config:
        task_data["output_files"] = config["output_files"]

    return task_data


def prepare_dataset(data_dir: Path, output_file: Path) -> None:
    if not data_dir.exists():
        logger.error(f"Data directory not found: {data_dir}")
        sys.exit(1)

    tasks = []
    for item in sorted(data_dir.iterdir()):
        if not item.is_dir():
            continue

        if (item / "config.json").exists():
            try:
                task = load_task_from_folder(item)
                tasks.append(task)
                logger.info(f"Loaded: {task['instance_id']}")
            except Exception as e:
                logger.warning(f"Skipped {item.name}: {e}")
        else:
            for task_dir in sorted(item.iterdir()):
                if not task_dir.is_dir():
                    continue
                try:
                    task = load_task_from_folder(task_dir)
                    tasks.append(task)
                    logger.info(f"Loaded: {task['instance_id']}")
                except Exception as e:
                    logger.warning(f"Skipped {task_dir.name}: {e}")

    if not tasks:
        logger.error("No tasks found")
        sys.exit(1)

    output_file.parent.mkdir(parents=True, exist_ok=True)
    with output_file.open("w") as f:
        for task in tasks:
            f.write(json.dumps(task) + "\n")

    logger.info(f"Wrote {len(tasks)} tasks to {output_file}")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Prepare dataset from task folders")
    parser.add_argument(
        "--data-dir", type=str, default="data", help="Data directory (default: data)"
    )
    parser.add_argument(
        "--output",
        type=str,
        default="data/tasks.jsonl",
        help="Output file (default: data/tasks.jsonl)",
    )

    args = parser.parse_args()
    logger.remove()
    logger.add(sys.stderr, level="INFO", format="<level>{message}</level>", colorize=True)

    prepare_dataset(Path(args.data_dir), Path(args.output))
