import json
from pathlib import Path
from typing import Any
from loguru import logger


def save_trajectory(messages: list[dict[str, Any]], output_file: Path | str) -> None:
    output_path = Path(output_file)
    output_path.parent.mkdir(parents=True, exist_ok=True)

    with output_path.open("w", encoding="utf-8") as f:
        for idx, message in enumerate(messages):
            if "step" not in message:
                message = {**message, "step": idx}
            json.dump(message, f, ensure_ascii=False)
            f.write("\n")


def load_trajectory(file_path: Path | str) -> list[dict[str, Any]]:
    file_path = Path(file_path)

    if not file_path.exists():
        logger.error(f"Trajectory file not found: {file_path}")
        raise FileNotFoundError(f"Trajectory file not found: {file_path}")

    logger.debug(f"Loading trajectory from: {file_path}")

    messages = []
    with file_path.open("r", encoding="utf-8") as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:  # Skip empty lines
                continue

            try:
                message = json.loads(line)
                messages.append(message)
            except json.JSONDecodeError as e:
                logger.error(f"Failed to parse line {line_num}: {e}")
                raise ValueError(f"Invalid JSON on line {line_num}: {e}") from e

    logger.info(f"Loaded trajectory: {len(messages)} messages")
    return messages
