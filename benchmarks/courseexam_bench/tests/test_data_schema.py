import json
from pathlib import Path
import pytest
import re

DATA_DIR = Path(__file__).parent.parent / "data"


def load_questions():
    questions_file = DATA_DIR / "questions.jsonl"
    questions = []
    with questions_file.open("r") as f:
        for line in f:
            if line.strip():
                questions.append(json.loads(line))
    return questions


def load_exams_metadata():
    metadata_file = DATA_DIR / "exams_metadata.json"
    with metadata_file.open("r") as f:
        data = json.load(f)
    return data["exams"]


class TestDataStructure:
    def test_data_dir_exists(self):
        assert DATA_DIR.exists(), f"Data directory not found: {DATA_DIR}"

    def test_questions_file_exists(self):
        questions_file = DATA_DIR / "questions.jsonl"
        assert questions_file.exists(), "questions.jsonl not found"

    def test_exams_metadata_exists(self):
        metadata_file = DATA_DIR / "exams_metadata.json"
        assert metadata_file.exists(), "exams_metadata.json not found"

    def test_reference_materials_dir_exists(self):
        ref_dir = DATA_DIR / "reference_materials"
        assert ref_dir.exists(), "reference_materials directory not found"


class TestQuestionsSchema:
    def test_questions_valid_json(self):
        questions = load_questions()
        assert len(questions) > 0, "No questions found in questions.jsonl"

    def test_questions_required_fields(self):
        questions = load_questions()
        required_fields = [
            "instance_id",
            "exam_id",
            "problem_id",
            "points",
            "problem",
            "answer",
            "type",
            "tags",
        ]

        for q in questions:
            for field in required_fields:
                assert (
                    field in q
                ), f"Question {q.get('instance_id', '?')} missing required field: {field}"

    def test_instance_ids_unique(self):
        questions = load_questions()
        instance_ids = [q["instance_id"] for q in questions]
        assert len(instance_ids) == len(
            set(instance_ids)
        ), "Duplicate instance_ids found"

    def test_instance_ids_incremental(self):
        questions = load_questions()
        instance_ids = sorted([q["instance_id"] for q in questions])

        for i in range(len(instance_ids) - 1):
            expected_next = instance_ids[i] + 1
            actual_next = instance_ids[i + 1]
            assert (
                actual_next == expected_next
            ), f"instance_ids not incremental: found {instance_ids[i]} then {actual_next}, expected {expected_next}"

    def test_instance_id_type(self):
        questions = load_questions()
        for q in questions:
            assert isinstance(
                q["instance_id"], int
            ), f"instance_id must be integer: {q['instance_id']}"
            assert (
                q["instance_id"] > 0
            ), f"instance_id must be positive: {q['instance_id']}"

    def test_exam_id_type(self):
        questions = load_questions()
        for q in questions:
            assert isinstance(
                q["exam_id"], str
            ), f"exam_id must be string in question {q['instance_id']}"
            assert (
                len(q["exam_id"]) > 0
            ), f"exam_id cannot be empty in question {q['instance_id']}"

    def test_exam_id_exists_in_metadata(self):
        questions = load_questions()
        exams = load_exams_metadata()

        exam_ids_in_metadata = {e["exam_id"] for e in exams}

        for q in questions:
            exam_id = q["exam_id"]
            assert (
                exam_id in exam_ids_in_metadata
            ), f"Question {q['instance_id']}: exam_id '{exam_id}' not found in exams_metadata.json"

    def test_points_type(self):
        questions = load_questions()
        for q in questions:
            assert isinstance(
                q["points"], int
            ), f"points must be integer in question {q['instance_id']}"
            assert (
                q["points"] > 0
            ), f"points must be positive in question {q['instance_id']}"

    def test_problem_type(self):
        questions = load_questions()
        for q in questions:
            assert isinstance(
                q["problem"], str
            ), f"problem must be string in question {q['instance_id']}"
            assert (
                len(q["problem"]) > 0
            ), f"problem cannot be empty in question {q['instance_id']}"

    def test_answer_type(self):
        questions = load_questions()
        for q in questions:
            assert isinstance(
                q["answer"], str
            ), f"answer must be string in question {q['instance_id']}"
            assert (
                len(q["answer"]) > 0
            ), f"answer cannot be empty in question {q['instance_id']}"

    def test_question_type_valid(self):
        questions = load_questions()
        valid_types = ["ExactMatch", "Freeform"]

        for q in questions:
            assert (
                q["type"] in valid_types
            ), f"Invalid type '{q['type']}' in question {q['instance_id']}. Must be one of {valid_types}"

    def test_tags_format(self):
        questions = load_questions()

        for q in questions:
            assert isinstance(
                q["tags"], list
            ), f"tags must be list in question {q['instance_id']}"
            assert (
                len(q["tags"]) >= 1
            ), f"At least one tag required in question {q['instance_id']}"

            for tag in q["tags"]:
                assert isinstance(
                    tag, str
                ), f"Each tag must be string in question {q['instance_id']}"
                assert re.match(
                    r"^[a-z0-9-]+$", tag
                ), f"Invalid tag format '{tag}' in question {q['instance_id']}. Use lowercase with hyphens"

    def test_reference_materials_format(self):
        questions = load_questions()

        for q in questions:
            if "reference_materials" in q:
                assert isinstance(
                    q["reference_materials"], list
                ), f"reference_materials must be list in question {q['instance_id']}"

                for ref in q["reference_materials"]:
                    assert isinstance(
                        ref, str
                    ), f"Each reference_material must be string in question {q['instance_id']}"
                    assert ref.startswith(
                        "reference_materials/"
                    ), f"Reference path must start with 'reference_materials/' in question {q['instance_id']}"
                    assert ref.endswith(
                        ".md"
                    ), f"Reference material must be .md file in question {q['instance_id']}"

    def test_reference_materials_exist(self):
        questions = load_questions()

        for q in questions:
            if "reference_materials" in q:
                for ref in q["reference_materials"]:
                    ref_path = DATA_DIR / ref
                    assert (
                        ref_path.exists()
                    ), f"Question {q['instance_id']}: reference material not found: {ref}"
                    assert (
                        ref_path.is_file()
                    ), f"Question {q['instance_id']}: reference material is not a file: {ref}"

    def test_llm_judge_instructions_format(self):
        questions = load_questions()

        for q in questions:
            if "llm_judge_instructions" in q:
                assert isinstance(
                    q["llm_judge_instructions"], str
                ), f"llm_judge_instructions must be string in question {q['instance_id']}"
                assert (
                    len(q["llm_judge_instructions"]) >= 20
                ), f"llm_judge_instructions too short in question {q['instance_id']}"


class TestExamsMetadata:
    def test_metadata_valid_json(self):
        exams = load_exams_metadata()
        assert len(exams) > 0, "No exams found in exams_metadata.json"

    def test_metadata_required_fields(self):
        exams = load_exams_metadata()
        required_fields = [
            "exam_id",
            "test_paper_name",
            "course",
            "year",
            "score_total",
            "num_questions",
        ]

        for exam in exams:
            for field in required_fields:
                assert (
                    field in exam
                ), f"Exam {exam.get('exam_id', '?')} missing required field: {field}"

    def test_exam_ids_unique(self):
        exams = load_exams_metadata()
        exam_ids = [e["exam_id"] for e in exams]
        assert len(exam_ids) == len(set(exam_ids)), "Duplicate exam_ids found"

    def test_exam_id_type(self):
        exams = load_exams_metadata()
        for exam in exams:
            assert isinstance(
                exam["exam_id"], str
            ), f"exam_id must be string: {exam['exam_id']}"

    def test_score_total_type(self):
        exams = load_exams_metadata()
        for exam in exams:
            assert isinstance(
                exam["score_total"], (int, float)
            ), f"score_total must be number in exam {exam['exam_id']}"
            assert (
                exam["score_total"] > 0
            ), f"score_total must be positive in exam {exam['exam_id']}"

    def test_num_questions_type(self):
        exams = load_exams_metadata()
        for exam in exams:
            assert isinstance(
                exam["num_questions"], int
            ), f"num_questions must be integer in exam {exam['exam_id']}"
            assert (
                exam["num_questions"] > 0
            ), f"num_questions must be positive in exam {exam['exam_id']}"


class TestDataConsistency:
    def test_points_sum_matches_metadata(self):
        """Verify sum of question points matches exam metadata score_total"""
        questions = load_questions()
        exams = load_exams_metadata()

        for exam in exams:
            exam_id = exam["exam_id"]
            exam_questions = [q for q in questions if q["exam_id"] == exam_id]

            total_points = sum(q["points"] for q in exam_questions)
            expected_points = exam["score_total"]

            assert (
                total_points == expected_points
            ), f"Exam {exam_id}: sum of question points ({total_points}) doesn't match score_total ({expected_points})"

    def test_question_count_matches_metadata(self):
        """Verify number of questions matches exam metadata num_questions"""
        questions = load_questions()
        exams = load_exams_metadata()

        for exam in exams:
            exam_id = exam["exam_id"]
            exam_questions = [q for q in questions if q["exam_id"] == exam_id]

            actual_count = len(exam_questions)
            expected_count = exam["num_questions"]

            assert (
                actual_count == expected_count
            ), f"Exam {exam_id}: actual question count ({actual_count}) doesn't match num_questions ({expected_count})"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
