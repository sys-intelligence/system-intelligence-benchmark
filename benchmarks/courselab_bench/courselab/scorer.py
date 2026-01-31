from pathlib import Path
from inspect_ai.scorer import Score, Scorer, Target, accuracy, scorer
from inspect_ai.solver import TaskState
from inspect_ai.util import sandbox


@scorer(metrics=[accuracy()])
def lab_scorer() -> Scorer:
    async def score(state: TaskState, target: Target) -> Score:
        task_folder = Path(state.metadata["task_folder"])
        evaluate_script = (task_folder / "evaluate.sh").read_text()

        await sandbox().write_file("evaluate.sh", evaluate_script)
        await sandbox().exec(["chmod", "+x", "evaluate.sh"])

        result = await sandbox().exec(["bash", "evaluate.sh"])

        artifacts = {}
        artifact_patterns = state.metadata.get("artifacts", [])
        if artifact_patterns:
            for pattern in artifact_patterns:
                glob_result = await sandbox().exec(
                    ["bash", "-c", f"ls {pattern} 2>/dev/null || true"]
                )
                if glob_result.success and glob_result.stdout.strip():
                    for file_path in glob_result.stdout.strip().split("\n"):
                        try:
                            content = await sandbox().read_file(file_path)
                            artifacts[file_path] = content
                        except Exception as e:
                            artifacts[file_path] = f"Error reading file: {str(e)}"

        if result.success:
            return Score(
                value="C",
                answer="PASS",
                explanation=result.stdout,
                metadata={"artifacts": artifacts} if artifacts else None,
            )
        else:
            return Score(
                value="I",
                answer="FAIL",
                explanation=result.stderr or result.stdout,
                metadata={"artifacts": artifacts} if artifacts else None,
            )

    return score
