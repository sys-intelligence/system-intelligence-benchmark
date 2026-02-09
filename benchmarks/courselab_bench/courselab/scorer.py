from pathlib import Path
from inspect_ai.scorer import Score, Scorer, Target, accuracy, scorer
from inspect_ai.solver import TaskState
from inspect_ai.util import sandbox


@scorer(metrics=[accuracy()])
def lab_scorer() -> Scorer:
    async def score(state: TaskState, target: Target) -> Score:
        task_folder = Path(state.metadata["task_folder"])
        
        # Check if this is a multi-round task
        if state.metadata.get("multi_round", False):
            # Multi-round task: evaluate each round and take AND of results
            num_rounds = state.metadata["num_rounds"]
            round_results = []
            all_passed = True
            combined_explanation = []
            
            for round_num in range(1, num_rounds + 1):
                evaluate_file = task_folder / f"evaluate{round_num}.sh"
                
                if not evaluate_file.exists():
                    # If evaluateX.sh doesn't exist, skip this round
                    combined_explanation.append(f"Round {round_num}: evaluate{round_num}.sh not found, skipping")
                    continue
                
                evaluate_script = evaluate_file.read_text()
                script_name = f"evaluate{round_num}.sh"
                
                await sandbox().write_file(script_name, evaluate_script)
                await sandbox().exec(["chmod", "+x", script_name])
                
                result = await sandbox().exec(["bash", script_name])
                
                round_passed = result.success
                all_passed = all_passed and round_passed
                
                round_results.append({
                    "round": round_num,
                    "passed": round_passed,
                    "stdout": result.stdout,
                    "stderr": result.stderr,
                })
                
                combined_explanation.append(
                    f"Round {round_num}: {'PASS' if round_passed else 'FAIL'}\n"
                    f"{result.stdout}\n"
                    f"{result.stderr if result.stderr else ''}"
                )
            
            # Collect artifacts after all rounds
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
            
            explanation = "\n\n".join(combined_explanation)
            metadata = {
                "round_results": round_results,
                "artifacts": artifacts if artifacts else None,
            }
            
            if all_passed:
                return Score(
                    value="C",
                    answer="PASS",
                    explanation=explanation,
                    metadata=metadata,
                )
            else:
                return Score(
                    value="I",
                    answer="FAIL",
                    explanation=explanation,
                    metadata=metadata,
                )
        else:
            # Single-round task: use existing logic
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
