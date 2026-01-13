import re

from inspect_ai.model import get_model
from inspect_ai.scorer import (
    Score,
    Scorer,
    Target,
    accuracy,
    choice,
    mean,
    scorer,
    stderr,
)
from inspect_ai.solver import TaskState


@scorer(metrics=[accuracy(), stderr(), mean()])
def exam_scorer(judge_model: str = "openai/gpt-4o-mini") -> Scorer:
    async def score(state: TaskState, target: Target) -> Score:
        question_type = state.metadata.get("type", "ExactMatch")
        points_possible = state.metadata.get("points", 1)

        if question_type == "ExactMatch":
            choice_scorer = choice()
            result = await choice_scorer(state, target)

            is_correct = result.value == "C"
            points_earned = points_possible if is_correct else 0

            return Score(
                value=result.value,
                answer=result.answer,
                explanation=result.explanation,
                metadata={
                    "points_earned": points_earned,
                    "points_possible": points_possible,
                },
            )

        model_answer = state.output.completion.strip()

        custom_instructions = state.metadata.get("llm_judge_instructions", "")

        grading_prompt = f"""You are grading a student's answer to an exam question.

Question: {state.input_text}

Correct Answer: {target.text}

Student's Answer: {model_answer}

Grading Instructions:
This question is worth {points_possible} points. Evaluate the student's answer for correctness, completeness, and clarity.

{custom_instructions}

Provide your grading in the following format:
1. First, explain your reasoning
2. Then provide the final score in the exact format: POINTS: X/{points_possible}

Where X is the number of points earned (0 to {points_possible}).
"""

        grader_model = get_model(judge_model)
        result = await grader_model.generate(grading_prompt)
        judge_output = result.completion

        points_pattern = r"POINTS:\s*(\d+(?:\.\d+)?)\s*/\s*(\d+)"
        match = re.search(points_pattern, judge_output)

        if match:
            points_earned = float(match.group(1))
            points_earned = max(0, min(points_earned, points_possible))

            percentage = points_earned / points_possible if points_possible > 0 else 0
            if percentage >= 1.0:
                value = "C"
            elif percentage == 0:
                value = "I"
            else:
                value = "P"

            return Score(
                value=value,
                answer=model_answer,
                explanation=judge_output,
                metadata={
                    "points_earned": points_earned,
                    "points_possible": points_possible,
                },
            )

        return Score(
            value="I",
            answer=model_answer,
            explanation=f"Failed to parse judge output: {judge_output}",
            metadata={
                "points_earned": 0,
                "points_possible": points_possible,
            },
        )

    return score
