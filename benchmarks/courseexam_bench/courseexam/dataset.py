import json
from pathlib import Path
from typing import Any

from inspect_ai.dataset import Dataset, Sample, json_dataset


def get_data_dir() -> Path:
    return Path(__file__).parent.parent / "data"


def load_exam_metadata() -> dict[str, Any]:
    data_dir = get_data_dir()
    metadata_file = data_dir / "exams_metadata.json"

    if not metadata_file.exists():
        raise FileNotFoundError(f"Exam metadata not found at {metadata_file}")

    return json.loads(metadata_file.read_text())


def load_reference_material(ref_path: str) -> str:
    data_dir = get_data_dir()
    full_path = data_dir / ref_path

    if not full_path.exists():
        raise FileNotFoundError(f"Reference material not found: {full_path}")

    return full_path.read_text()


def record_to_sample(record: dict[str, Any]) -> Sample:
    input_text = record["input"]

    ref_materials = record.get("metadata", {}).get("reference_materials", [])
    if ref_materials:
        refs_content = []
        for ref_path in ref_materials:
            try:
                content = load_reference_material(ref_path)
                refs_content.append(content)
            except FileNotFoundError:
                pass

        if refs_content:
            ref_section = "\n\n---\n\n## REFERENCE MATERIALS\n\n"
            ref_section += "\n\n---\n\n".join(refs_content)
            ref_section += "\n\n---\n\n"
            input_text = ref_section + input_text

    return Sample(
        id=record.get("id"),
        input=input_text,
        target=record["target"],
        choices=record.get("choices"),
        metadata=record.get("metadata", {}),
    )


def load_dataset(
    exam_ids: str | list[str] | None = None,
    question_types: str | list[str] | None = None,
    tags: str | list[str] | None = None,
    shuffle: bool = False,
) -> Dataset:
    data_dir = get_data_dir()
    questions_file = data_dir / "questions.jsonl"

    if not questions_file.exists():
        raise FileNotFoundError(f"Questions file not found at {questions_file}")

    mtime = questions_file.stat().st_mtime
    dataset = json_dataset(
        str(questions_file),
        sample_fields=record_to_sample,
        shuffle=shuffle,
        seed=42,
        name=f"courseexam_{mtime}",
    )

    if exam_ids:
        exam_ids = [exam_ids] if isinstance(exam_ids, str) else exam_ids
        dataset = dataset.filter(
            lambda s: s.metadata and s.metadata.get("exam_id") in exam_ids
        )

    if question_types:
        question_types = (
            [question_types] if isinstance(question_types, str) else question_types
        )
        dataset = dataset.filter(
            lambda s: s.metadata and s.metadata.get("type") in question_types
        )

    if tags:
        tags = [tags] if isinstance(tags, str) else tags
        dataset = dataset.filter(
            lambda s: s.metadata
            and any(tag in s.metadata.get("tags", []) for tag in tags)
        )

    return dataset
