from inspect_ai import Task, task
from inspect_ai.model import GenerateConfig
from inspect_ai.solver import (
    Generate,
    Solver,
    TaskState,
    generate,
    multiple_choice,
    solver,
)

from courseexam.dataset import load_dataset, load_exam_metadata
from courseexam.metrics import (
    points_accuracy,
    total_points_earned,
    total_points_possible,
)
from courseexam.scorer import exam_scorer


@solver
def conditional_solver() -> Solver:
    mc_solver = multiple_choice()
    gen_solver = generate()

    async def solve(state: TaskState, generate_fn: Generate) -> TaskState:
        question_type = state.metadata.get("type", "Freeform")

        if question_type == "ExactMatch":
            return await mc_solver(state, generate_fn)
        else:
            return await gen_solver(state, generate_fn)

    return solve


@task
def courseexam(
    exam_ids: str | list[str] | None = None,
    question_types: str | list[str] | None = None,
    tags: str | list[str] | None = None,
    shuffle: bool = False,
    max_tokens: int = 2048,
    judge_model: str = "openai/gpt-4o-mini",
) -> Task:
    dataset = load_dataset(
        exam_ids=exam_ids,
        question_types=question_types,
        tags=tags,
        shuffle=shuffle,
    )

    metadata = load_exam_metadata()

    exam_info = {
        "num_exams": len(metadata["exams"]),
        "exams": metadata["exams"],
    }

    return Task(
        dataset=dataset,
        solver=conditional_solver(),
        scorer=exam_scorer(judge_model=judge_model),
        metrics=[
            points_accuracy(),
            total_points_earned(),
            total_points_possible(),
        ],
        config=GenerateConfig(max_tokens=max_tokens, temperature=0.0),
        metadata=exam_info,
        name="courseexam",
        version="0.1.0",
    )
