import json
import re
from pathlib import Path
from typing import Any


def parse_exam_markdown(
    exam_md_path: Path,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    content = exam_md_path.read_text()

    exam_metadata_match = re.search(r"```json\n(\{.*?\})\n```", content, re.DOTALL)
    if not exam_metadata_match:
        raise ValueError(f"No exam metadata found in {exam_md_path}")

    exam_metadata = json.loads(exam_metadata_match.group(1))
    sections = content.split("\n---\n")[1:]
    samples = []

    for section in sections:
        json_blocks = re.findall(r"```json\n(\{.*?\})\n```", section, re.DOTALL)

        for json_block in json_blocks:
            question_data = json.loads(json_block)

            if "problem_id" not in question_data:
                continue

            question_start = section.find("##")
            question_end = section.find("```json")
            problem_text = section[question_start:question_end].strip()
            problem_text = re.sub(
                r"^## Question.*?\n+", "", problem_text, flags=re.MULTILINE
            ).strip()

            sample = {
                "input": problem_text,
                "target": question_data["answer"],
                "id": f"{exam_metadata['exam_id']}_{question_data['problem_id']}",
                "metadata": {
                    "exam_id": exam_metadata["exam_id"],
                    "problem_id": question_data["problem_id"],
                    "points": question_data["points"],
                    "type": question_data["type"],
                    "tags": question_data["tags"],
                },
            }

            if "choices" in question_data:
                sample["choices"] = question_data["choices"]

            if "reference_materials" in question_data:
                exam_folder = exam_md_path.parent
                data_dir = exam_folder.parent.parent
                ref_dir = data_dir / "reference_materials"
                ref_dir.mkdir(exist_ok=True)

                ref_materials = []
                for ref in question_data["reference_materials"]:
                    ref_path = exam_folder / ref
                    if ref_path.exists():
                        dest = ref_dir / ref
                        dest.write_text(ref_path.read_text())
                        ref_materials.append(f"reference_materials/{ref}")

                sample["metadata"]["reference_materials"] = ref_materials

            if "llm_judge_instructions" in question_data:
                sample["metadata"]["llm_judge_instructions"] = question_data[
                    "llm_judge_instructions"
                ]

            samples.append(sample)

    return exam_metadata, samples


def prepare_dataset(data_dir: Path) -> None:
    raw_dir = data_dir / "raw"
    all_exams_metadata = []
    all_samples = []

    for exam_folder in raw_dir.iterdir():
        if not exam_folder.is_dir():
            continue

        exam_md = exam_folder / "exam.md"
        if not exam_md.exists():
            continue

        exam_metadata, samples = parse_exam_markdown(exam_md)
        all_exams_metadata.append(exam_metadata)
        all_samples.extend(samples)

    questions_output = data_dir / "questions.jsonl"
    with questions_output.open("w") as f:
        for sample in all_samples:
            f.write(json.dumps(sample) + "\n")

    metadata_output = data_dir / "exams_metadata.json"
    metadata_output.write_text(json.dumps({"exams": all_exams_metadata}, indent=2))


if __name__ == "__main__":
    script_dir = Path(__file__).parent
    data_dir = script_dir.parent / "data"
    prepare_dataset(data_dir)
