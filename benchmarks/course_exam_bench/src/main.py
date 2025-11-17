"""Evaluate LLM performance on course exam benchmark."""

import argparse
import json
import os
import sys
from datetime import datetime

import pandas as pd

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../../../")))

from loguru import logger

from sdk.evaluator import ExamEvaluator
from sdk.executor import SimpleExecutor
from sdk.utils import set_llm_endpoint_from_config

FORMAT_INSTRUCTIONS = {
    "SingleChoice": """
This is a Single-choice problem.

Please return your response in the following JSON format:
```json
{"answer": "A", "explanation": "Your explanation here."}
```
""",
    "MultipleChoice": """
This is a MultipleChoice problem.

Please return your response in the following JSON format:
```json
{"answer": "A,B,C", "explanation": "Your explanation here."}
```

answer is capital letters separated by commas, without spaces
""",
    "True/False Questions": """
This is a True/False problem.

Please return your response in the following JSON format:
```json
{"answer": "True,False,True", "explanation": "Your explanation here."}
```

answer is each item corresponds to a sub-question
""",
    "ShortAnswerQuestion": """
This is a ShortAnswerQuestion problem.

Please return your response in the following JSON format:
```json
{"answer": "Your answer here.", "explanation": "Your explanation here."}
```
""",
}


def load_benchmark_data(data_dir):
    """Load benchmark data from exam metadata and questions files.

    Args:
        data_dir: Directory containing exams_metadata.json and questions.jsonl

    Returns:
        Tuple of (questions list, exams metadata dict)
    """
    metadata_file = os.path.join(data_dir, "exams_metadata.json")
    questions_file = os.path.join(data_dir, "questions.jsonl")

    with open(metadata_file, encoding="utf-8") as f:
        metadata = json.load(f)
        exams_dict = {exam["exam_id"]: exam for exam in metadata["exams"]}

    # Load questions and join with exam metadata
    questions = []
    with open(questions_file, encoding="utf-8") as f:
        for line in f:
            question = json.loads(line)
            exam = exams_dict[question["exam_id"]]

            # Merge question with exam metadata
            groundtruth = {
                "instance_id": question["instance_id"],
                "exam_id": question["exam_id"],
                "test_paper_name": exam["test_paper_name"],
                "course": exam["course"],
                "year": exam["year"],
                "problem_num": question["problem_num"],
                "points": question["points"],
                "score_total": exam["score_total"],
                "score_max": exam["score_max"],
                "score_avg": exam["score_avg"],
                "score_median": exam["score_median"],
                "problem": question["problem"],
                "answer": question["answer"],
                "explanation": question["explanation"],
                "type": question["type"],
            }
            questions.append(groundtruth)

    return questions, exams_dict


def process_question(groundtruth, model_name, agent_name, exam_id):
    """Process a single question: prompt LLM and evaluate response.

    Args:
        groundtruth: Question data with correct answer
        model_name: Name of the LLM model
        agent_name: Type of agent to use
        exam_id: Exam identifier

    Returns:
        Tuple of (minimal_result, detailed_result)
    """
    format_instruction = FORMAT_INSTRUCTIONS.get(
        groundtruth["type"], FORMAT_INSTRUCTIONS["ShortAnswerQuestion"]
    )
    system_prompt = (
        f"You are a university student who has completed the {groundtruth['course']} course. "
        f"You are now answering a final exam question." + format_instruction
    )
    user_prompt = f"Below is the problem description:\n{groundtruth['problem']}"

    try:
        if agent_name == "llm":
            executor = SimpleExecutor(model_name, system_prompt)
        else:
            raise ValueError(f"Unknown agent name: {agent_name}")

        response_text = executor.run(user_prompt, lang="json")
        response = json.loads(response_text)
        llm_answer = str(response.get("answer", ""))
        llm_explanation = response.get("explanation", "")

        logger.info(f'Question {groundtruth["instance_id"]}: Answer={llm_answer}')

        evaluator = ExamEvaluator()
        metrics = evaluator.eval(
            llm_answer=llm_answer, groundtruth=groundtruth, model_name=model_name
        )
        points_earned = int(metrics["llm_score"])
        points_possible = groundtruth["points"]
        if points_earned == points_possible:
            status = "correct"
        elif points_earned > 0:
            status = "partial"
        else:
            status = "incorrect"

        minimal_result = {
            "instance_id": groundtruth["instance_id"],
            "exam_id": exam_id,
            "question_type": groundtruth["type"],
            "llm_answer": llm_answer,
            "correct_answer": groundtruth["answer"],
            "points_earned": points_earned,
            "points_possible": points_possible,
            "status": status,
        }
        detailed_result = {
            **minimal_result,
            "problem": groundtruth["problem"],
            "llm_explanation": llm_explanation,
            "correct_explanation": groundtruth["explanation"],
            "llmjudger_explanation": metrics["llmjudger_explanation"],
            "system_prompt": system_prompt,
            "user_prompt": user_prompt,
        }
    except Exception as e:
        logger.error(f"Error processing question {groundtruth['instance_id']}: {e}")
        minimal_result = {
            "instance_id": groundtruth["instance_id"],
            "exam_id": exam_id,
            "question_type": groundtruth["type"],
            "llm_answer": None,
            "correct_answer": groundtruth["answer"],
            "points_earned": 0,
            "points_possible": groundtruth["points"],
            "status": "error",
            "error": str(e),
        }
        detailed_result = {
            **minimal_result,
            "problem": groundtruth["problem"],
            "llm_explanation": None,
            "correct_explanation": groundtruth["explanation"],
            "system_prompt": system_prompt,
            "user_prompt": user_prompt,
        }
    return minimal_result, detailed_result


def compute_summary(results_df, exams_metadata):
    """Compute summary statistics using pandas.

    Args:
        results_df: DataFrame with evaluation results
        exams_metadata: Dictionary mapping exam_id to exam metadata

    Returns:
        Tuple of (summary dict, comparison dict)
    """
    total_questions = len(results_df)
    answered = len(results_df[results_df["status"] != "error"])
    unanswered = total_questions - answered
    correct = len(results_df[results_df["status"] == "correct"])
    incorrect = len(results_df[results_df["status"].isin(["incorrect", "partial"])])
    points_earned = int(results_df["points_earned"].sum())
    points_possible = int(results_df["points_possible"].sum())
    summary = {
        "overall": {
            "total_questions": total_questions,
            "answered": answered,
            "unanswered": unanswered,
            "correct": correct,
            "incorrect": incorrect,
            "points_earned": points_earned,
            "points_possible": points_possible,
            "accuracy": round(correct / answered, 3) if answered > 0 else 0,
            "score_percentage": (
                round(points_earned / points_possible, 3) if points_possible > 0 else 0
            ),
        }
    }
    # By exam summary
    by_exam = []
    for exam_id in results_df["exam_id"].unique():
        exam_results = results_df[results_df["exam_id"] == exam_id]
        exam_meta = exams_metadata.get(exam_id, {})
        exam_answered = len(exam_results[exam_results["status"] != "error"])
        exam_correct = len(exam_results[exam_results["status"] == "correct"])
        exam_points_earned = int(exam_results["points_earned"].sum())
        exam_points_possible = int(exam_results["points_possible"].sum())
        by_exam.append(
            {
                "exam_id": exam_id,
                "exam_name": exam_meta.get("test_paper_name", exam_id),
                "total_questions": len(exam_results),
                "answered": exam_answered,
                "correct": exam_correct,
                "incorrect": exam_answered - exam_correct,
                "points_earned": exam_points_earned,
                "points_possible": exam_points_possible,
                "accuracy": (
                    round(exam_correct / exam_answered, 3) if exam_answered > 0 else 0
                ),
                "score_percentage": (
                    round(exam_points_earned / exam_points_possible, 3)
                    if exam_points_possible > 0
                    else 0
                ),
            }
        )
    summary["by_exam"] = by_exam
    # Comparison with student performance
    comparison = {"exams": []}
    for exam_id in results_df["exam_id"].unique():
        exam_results = results_df[results_df["exam_id"] == exam_id]
        exam_meta = exams_metadata.get(exam_id, {})

        if not exam_meta:
            continue

        exam_points_earned = int(exam_results["points_earned"].sum())
        exam_points_possible = int(exam_results["points_possible"].sum())
        comparison["exams"].append(
            {
                "exam_id": exam_id,
                "exam_name": exam_meta.get("test_paper_name", exam_id),
                "llm_performance": {
                    "points_earned": exam_points_earned,
                    "points_possible": exam_points_possible,
                    "percentage": (
                        round(exam_points_earned / exam_points_possible, 3)
                        if exam_points_possible > 0
                        else 0
                    ),
                },
                "student_baseline": {
                    "average_score": exam_meta.get("score_avg", 0),
                    "max_score": exam_meta.get("score_max", 0),
                    "median_score": exam_meta.get("score_median", 0),
                    "total_points": exam_meta.get("score_total", 0),
                    "average_percentage": (
                        round(
                            exam_meta.get("score_avg", 0)
                            / exam_meta.get("score_total", 1),
                            3,
                        )
                        if exam_meta.get("score_total", 0) > 0
                        else 0
                    ),
                },
            }
        )
    return summary, comparison


def main(data_dir, output_dir, model_name, agent_name):
    """Run the course exam benchmark.

    Args:
        data_dir: Directory containing benchmark data files
        output_dir: Directory to save results
        model_name: Name of the LLM model
        agent_name: Type of agent to use
    """
    logger.info("Loading benchmark data...")
    questions, exams_metadata = load_benchmark_data(data_dir)
    logger.info(f"Loaded {len(questions)} questions from {len(exams_metadata)} exams")
    minimal_results = []
    detailed_results = []

    # Streaming
    results_file = os.path.join(output_dir, "results.jsonl")
    detailed_file = os.path.join(output_dir, "results_detailed.jsonl")

    with open(results_file, "w", encoding="utf-8") as f_minimal, open(
        detailed_file, "w", encoding="utf-8"
    ) as f_detailed:
        for groundtruth in questions:
            logger.info(f"========== Question {groundtruth['instance_id']} ==========")
            minimal_result, detailed_result = process_question(
                groundtruth, model_name, agent_name, groundtruth["exam_id"]
            )
            minimal_results.append(minimal_result)
            detailed_results.append(detailed_result)
            f_minimal.write(json.dumps(minimal_result, ensure_ascii=False) + "\n")
            f_detailed.write(json.dumps(detailed_result, ensure_ascii=False) + "\n")

    results_df = pd.DataFrame(minimal_results)
    summary, comparison = compute_summary(results_df, exams_metadata)

    summary_file = os.path.join(output_dir, "summary.json")
    with open(summary_file, "w", encoding="utf-8") as f:
        json.dump(summary, f, indent=2, ensure_ascii=False)
    comparison_file = os.path.join(output_dir, "comparison.json")
    with open(comparison_file, "w", encoding="utf-8") as f:
        json.dump(comparison, f, indent=2, ensure_ascii=False)


if __name__ == "__main__":
    # Load LLM endpoint configuration
    set_llm_endpoint_from_config("env.toml")

    parser = argparse.ArgumentParser(description="Course Exam Benchmark")
    parser.add_argument(
        "-d",
        "--data_dir",
        help="Directory containing exams_metadata.json and questions.jsonl",
        default="./data/benchmark",
    )
    parser.add_argument(
        "-o", "--output_dir", help="Output directory for results", default=None
    )
    parser.add_argument("-a", "--agent", help="Agent type", default="llm")
    parser.add_argument("-m", "--model_name", help="Model name", required=True)
    args = parser.parse_args()
    if args.output_dir is None:
        model_name_safe = args.model_name.replace("/", "_")
        timestamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        output_dir = os.path.join(
            "./outputs", f"course_exam__{model_name_safe}__{args.agent}__{timestamp}"
        )
    else:
        output_dir = args.output_dir
    output_dir = os.path.abspath(os.path.expanduser(output_dir))
    os.makedirs(output_dir, exist_ok=True)

    main(args.data_dir, output_dir, args.model_name, args.agent)
