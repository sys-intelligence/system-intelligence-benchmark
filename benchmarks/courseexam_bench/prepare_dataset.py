import json
import re
from pathlib import Path


def parse_exam_markdown(exam_md_path, start_instance_id):
    content = exam_md_path.read_text()

    exam_metadata_match = re.search(r"```json\n(\{[^`]+?\})\n```", content)
    exam_metadata = json.loads(exam_metadata_match.group(1))

    sections = content.split("\n---\n")[1:]

    questions = []
    instance_id = start_instance_id

    for section in sections:
        json_blocks = re.findall(r"```json\n(\{[^`]+?\})\n```", section)

        for json_block in json_blocks:
            question_data = json.loads(json_block)

            if "problem_id" not in question_data:
                continue

            question_start = section.find("##")
            question_end = section.find("```json")
            problem_text = section[question_start:question_end].strip()
            problem_text = re.sub(
                r"^## Question.*?\n+", "", problem_text, flags=re.MULTILINE
            )
            problem_text = problem_text.strip()

            question = {
                "instance_id": instance_id,
                "exam_id": exam_metadata["exam_id"],
                "problem_id": question_data["problem_id"],
                "points": question_data["points"],
                "problem": problem_text,
                "answer": question_data["answer"],
                "type": question_data["type"],
                "tags": question_data["tags"],
            }

            if "reference_materials" in question_data:
                ref_materials = []
                exam_folder = exam_md_path.parent
                data_dir = exam_folder.parent
                ref_dir = data_dir / "reference_materials"
                ref_dir.mkdir(exist_ok=True)
                for ref in question_data["reference_materials"]:
                    ref_path = exam_folder / ref
                    if ref_path.exists():
                        dest = ref_dir / ref
                        dest.write_text(ref_path.read_text())
                    ref_materials.append(f"reference_materials/{ref}")
                question["reference_materials"] = ref_materials

            if "llm_judge_instructions" in question_data:
                question["llm_judge_instructions"] = question_data[
                    "llm_judge_instructions"
                ]

            if "comments" in question_data:
                question["comments"] = question_data["comments"]

            questions.append(question)
            instance_id += 1

    return exam_metadata, questions, instance_id


def main():
    script_dir = Path(__file__).parent
    data_dir = script_dir / "data"

    all_exams_metadata = []
    all_questions = []
    next_instance_id = 1

    for exam_folder in data_dir.iterdir():
        if not exam_folder.is_dir() or exam_folder.name in [
            "reference_materials",
            "example_exam",
        ]:
            continue

        exam_md = exam_folder / "exam.md"
        if not exam_md.exists():
            continue

        exam_metadata, questions, next_instance_id = parse_exam_markdown(
            exam_md, next_instance_id
        )
        all_exams_metadata.append(exam_metadata)
        all_questions.extend(questions)

    metadata_output = data_dir / "exams_metadata.json"
    metadata_output.write_text(json.dumps({"exams": all_exams_metadata}, indent=2))

    questions_output = data_dir / "questions.jsonl"
    with questions_output.open("w") as f:
        for q in all_questions:
            f.write(json.dumps(q) + "\n")


if __name__ == "__main__":
    main()
