"""Tests for the course exam benchmark."""

import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch
import sys

sys.path.insert(0, str(Path(__file__).parent.parent / "src"))
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))


class TestBenchmarkData(unittest.TestCase):
    def setUp(self):
        self.benchmark_dir = Path(__file__).parent.parent / "data" / "benchmark"
        self.metadata_path = self.benchmark_dir / "exams_metadata.json"
        self.questions_path = self.benchmark_dir / "questions.jsonl"

    def test_required_files_exist(self):
        self.assertTrue(
            self.metadata_path.exists(),
            f"Exam metadata file not found: {self.metadata_path}",
        )
        self.assertTrue(
            self.questions_path.exists(),
            f"Questions file not found: {self.questions_path}",
        )

    def test_metadata_schema(self):
        with open(self.metadata_path, encoding="utf-8") as f:
            metadata = json.load(f)
        self.assertIn("exams", metadata, "Metadata must have 'exams' key")
        self.assertIsInstance(metadata["exams"], list, "'exams' must be a list")
        self.assertGreater(len(metadata["exams"]), 0, "Must have at least one exam")
        required_fields = [
            "exam_id",
            "test_paper_name",
            "course",
            "year",
            "score_total",
            "score_max",
            "score_avg",
            "score_median",
            "score_standard_deviation",
            "num_questions",
        ]

        for i, exam in enumerate(metadata["exams"]):
            for field in required_fields:
                self.assertIn(field, exam, f'Exam {i}: missing field "{field}"')

            # Check field types
            self.assertIsInstance(exam["exam_id"], str)
            self.assertIsInstance(exam["test_paper_name"], str)
            self.assertIsInstance(exam["course"], str)
            self.assertIsInstance(exam["year"], int)
            self.assertIsInstance(exam["num_questions"], int)
            # Check value constraints
            self.assertGreater(exam["num_questions"], 0)
            # I can't think of any other reasonable constraints for the scores for now

    def test_questions_schema(self):
        required_fields = [
            "instance_id",
            "exam_id",
            "problem_num",
            "points",
            "problem",
            "answer",
            "explanation",
            "type",
        ]
        valid_types = [
            "SingleChoice",
            "MultipleChoice",
            "True/False Questions",
            "ShortAnswerQuestion",
        ]
        instance_ids = set()
        question_count = 0
        with open(self.questions_path, encoding="utf-8") as f:
            for line_num, line in enumerate(f, 1):
                question = json.loads(line)
                question_count += 1
                for field in required_fields:
                    self.assertIn(
                        field, question, f'Line {line_num}: missing field "{field}"'
                    )
                self.assertIsInstance(question["instance_id"], int)
                self.assertIsInstance(question["exam_id"], str)
                self.assertIsInstance(question["problem_num"], int)
                self.assertIsInstance(question["points"], int)
                self.assertIsInstance(question["problem"], str)
                self.assertIsInstance(question["answer"], str)
                self.assertIsInstance(question["explanation"], str)
                self.assertIsInstance(question["type"], str)
                self.assertNotIn(
                    question["instance_id"],
                    instance_ids,
                    f'Line {line_num}: duplicate instance_id {question["instance_id"]}',
                )
                instance_ids.add(question["instance_id"])
                self.assertIn(
                    question["type"],
                    valid_types,
                    f'Line {line_num}: invalid type "{question["type"]}"',
                )
                self.assertGreater(len(question["problem"]), 0)
                self.assertGreater(len(question["answer"]), 0)
        self.assertGreater(question_count, 0, "Must have at least one question")

    def test_data_integrity(self):
        """Test that metadata and questions are consistent."""
        with open(self.metadata_path, encoding="utf-8") as f:
            metadata = json.load(f)
        exams_dict = {exam["exam_id"]: exam for exam in metadata["exams"]}
        # Load questions and count per exam
        question_counts = {}
        with open(self.questions_path, encoding="utf-8") as f:
            for line in f:
                question = json.loads(line)
                exam_id = question["exam_id"]
                # Check that exam_id exists in metadata
                self.assertIn(
                    exam_id,
                    exams_dict,
                    f"Question references non-existent exam_id: {exam_id}",
                )
                question_counts[exam_id] = question_counts.get(exam_id, 0) + 1
        # Verify question counts match metadata
        for exam_id, exam in exams_dict.items():
            actual_count = question_counts.get(exam_id, 0)
            expected_count = exam["num_questions"]
            self.assertEqual(
                actual_count,
                expected_count,
                f"Exam {exam_id}: metadata says {expected_count} questions, but found {actual_count}",
            )

    def test_questions_sorted(self):
        """Test that questions are sorted by exam_id then instance_id."""
        questions = []
        with open(self.questions_path, encoding="utf-8") as f:
            for line in f:
                questions.append(json.loads(line))
        for i in range(len(questions) - 1):
            curr = questions[i]
            next_q = questions[i + 1]
            # If same exam, instance_id should be increasing or equal
            if curr["exam_id"] == next_q["exam_id"]:
                self.assertLessEqual(
                    curr["instance_id"],
                    next_q["instance_id"],
                    f'Questions not sorted within exam {curr["exam_id"]}: '
                    f'instance_id {curr["instance_id"]} comes before {next_q["instance_id"]}',
                )


class TestBenchmarkOutput(unittest.TestCase):
    def test_output_format(self):
        """Test that benchmark generates expected output files with correct format."""
        import main
        from sdk.evaluator import ExamEvaluator
        from sdk.executor import SimpleExecutor

        with tempfile.TemporaryDirectory() as temp_dir:
            # Mock the LLM executor to avoid actual API calls
            with patch.object(SimpleExecutor, "__init__", return_value=None):
                with patch.object(
                    SimpleExecutor,
                    "run",
                    return_value='{"answer": "A", "explanation": "Test"}',
                ):
                    # Mock the evaluator
                    with patch.object(ExamEvaluator, "__init__", return_value=None):
                        with patch.object(
                            ExamEvaluator,
                            "eval",
                            return_value={
                                "llm_score": 5,
                                "llmjudger_explanation": None,
                                "llmjudger_system_prompt": None,
                            },
                        ):
                            data_dir = str(
                                Path(__file__).parent.parent / "data" / "benchmark"
                            )
                            main.main(data_dir, temp_dir, "test-model", "llm")
            expected_files = [
                "results.jsonl",
                "results_detailed.jsonl",
                "summary.json",
                "comparison.json",
            ]
            for filename in expected_files:
                filepath = Path(temp_dir) / filename
                self.assertTrue(
                    filepath.exists(),
                    f"Expected output file not found: {filename}",
                )

            # results.jsonl format
            results_file = Path(temp_dir) / "results.jsonl"
            with open(results_file, encoding="utf-8") as f:
                for line_num, line in enumerate(f, 1):
                    result = json.loads(line)
                    required_fields = [
                        "instance_id",
                        "exam_id",
                        "question_type",
                        "llm_answer",
                        "correct_answer",
                        "points_earned",
                        "points_possible",
                        "status",
                    ]
                    for field in required_fields:
                        self.assertIn(
                            field, result, f'Line {line_num}: missing field "{field}"'
                        )
                    # status is valid
                    valid_statuses = ["correct", "incorrect", "partial", "error"]
                    self.assertIn(result["status"], valid_statuses)
            # results_detailed.jsonl format
            detailed_file = Path(temp_dir) / "results_detailed.jsonl"
            with open(detailed_file, encoding="utf-8") as f:
                for line_num, line in enumerate(f, 1):
                    result = json.loads(line)
                    # has the additional fields
                    additional_fields = [
                        "problem",
                        "llm_explanation",
                        "correct_explanation",
                        "system_prompt",
                        "user_prompt",
                    ]
                    for field in additional_fields:
                        self.assertIn(
                            field,
                            result,
                            f'Detailed line {line_num}: missing field "{field}"',
                        )
            # summary.json format
            summary_file = Path(temp_dir) / "summary.json"
            with open(summary_file, encoding="utf-8") as f:
                summary = json.load(f)
                self.assertIn("overall", summary)
                overall_fields = [
                    "total_questions",
                    "answered",
                    "unanswered",
                    "correct",
                    "incorrect",
                    "points_earned",
                    "points_possible",
                    "accuracy",
                    "score_percentage",
                ]
                for field in overall_fields:
                    self.assertIn(field, summary["overall"])

                self.assertIn("by_exam", summary)
                self.assertIsInstance(summary["by_exam"], list)

            # comparison.json format
            comparison_file = Path(temp_dir) / "comparison.json"
            with open(comparison_file, encoding="utf-8") as f:
                comparison = json.load(f)
                self.assertIn("exams", comparison)
                self.assertIsInstance(comparison["exams"], list)
                if len(comparison["exams"]) > 0:
                    exam = comparison["exams"][0]
                    self.assertIn("exam_id", exam)
                    self.assertIn("exam_name", exam)
                    self.assertIn("llm_performance", exam)
                    self.assertIn("student_baseline", exam)


if __name__ == "__main__":
    unittest.main()
