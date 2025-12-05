import argparse
import datetime
import json
import os
import sys

# Add parent directory to path to allow importing sregym_core
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

try:
    from sregym_core.main import main as sregym_main
except ImportError:
    # In case sregym_core is not found in parent, try explicit path
    sys.path.append(
        os.path.abspath(os.path.join(os.path.dirname(__file__), "../sregym_core"))
    )
    from sregym_core.main import main as sregym_main


def main(input_file: str, output_dir: str, model_name: str, agent_name: str):
    # Set the environment variable for the model so the agent can find it
    os.environ["PROVIDER_OVERWRITE"] = model_name

    # Ensure output directory exists
    save_path = os.path.abspath(os.path.expanduser(output_dir))
    os.makedirs(save_path, exist_ok=True)

    scores = []

    with open(input_file) as f, open(
        os.path.join(output_dir, "result.jsonl"), "w"
    ) as out:
        for line in f:
            item = json.loads(line)
            task_id, task_name = item["id"], item["task_name"]
            print(f"\n{'='*70}\nTask: {task_id} ({task_name})\n{'='*70}")

            try:
                sregym_args = argparse.Namespace(
                    agent=agent_name,
                    model=model_name,
                    problem=task_name,
                    use_external_harness=False,
                )
                print(f"SREGym Main Arguments: \33[94m{sregym_args}\33[0m")

                result = sregym_main(sregym_args)

                if type(result) != list or len(result) != 1:
                    raise ValueError(f"Result is not a valid list: {result}")

                first_agent_result = result[0].get(agent_name, None)

                if first_agent_result is None:
                    raise ValueError(
                        f"Agent result for {agent_name} not found: {result}"
                    )

                if type(first_agent_result) != list or len(first_agent_result) != 1:
                    raise ValueError(
                        f"Agent result for {agent_name} is not a valid list: {first_agent_result}"
                    )

                first_problem_result = first_agent_result[0]

                print(f"SREGym Problem Result: \33[94m{first_problem_result}\33[0m")

                problem_id_ = first_problem_result.get("problem_id", None)
                if problem_id_ is None or problem_id_ != task_name:
                    raise ValueError(
                        f"Problem ID mismatch: {problem_id_} != {task_name}"
                    )
                diagnosis_result = first_problem_result.get("Diagnosis.success", None)
                mitigation_result = first_problem_result.get("Mitigation.success", None)
                diagnosis_time = first_problem_result.get("TTL", None)
                mitigation_time = first_problem_result.get("TTM", None)

                output = {
                    "id": task_id,
                    "task_name": task_name,
                    "model_name": model_name,
                }

                if diagnosis_result is not None:
                    output["diagnosis_success"] = diagnosis_result
                    output["diagnosis_time"] = diagnosis_time

                if mitigation_result is not None:
                    output["mitigation_success"] = mitigation_result
                    output["mitigation_time"] = mitigation_time

                if hasattr(result, "error") and result.error:
                    output["error"] = result.error

                all_success = output.get("diagnosis_success", True) and output.get(
                    "mitigation_success", True
                )
                scores.append(1.0 if all_success else 0.0)
            except Exception as e:
                print(f"\33[91mError: {e}\33[0m")
                output = {"id": task_id, "error": str(e), "final_score": 0.0}
                scores.append(0.0)

            out.write(json.dumps(output) + "\n")
            out.flush()

    # Save summary
    avg_score = {
        "final_score": sum(scores) / len(scores) if scores else 0.0,
        "total_tasks": len(scores),
    }
    with open(os.path.join(output_dir, "avg_score.json"), "w") as f:
        json.dump(avg_score, f, indent=2)

    print(f"\n{'='*70}\nFinal Score: {avg_score['final_score']:.3f}\n{'='*70}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="SREGym Benchmark Runner")
    parser.add_argument(
        "--input_file",
        type=str,
        default="./data/benchmark/tasks.jsonl",
        help="Path to input file",
    )
    parser.add_argument(
        "--output_dir", type=str, default=None, help="Path to output directory"
    )
    parser.add_argument("--model_name", type=str, default="openai", help="Model name")
    parser.add_argument("--agent_name", type=str, default="stratus", help="Agent name")

    args = parser.parse_args()
    if args.output_dir is None:
        timestamp = datetime.datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        args.output_dir = f"./outputs/sregym__{args.model_name.replace('/', '_')}__{args.agent_name}___{timestamp}"

    main(args.input_file, args.output_dir, args.model_name, args.agent_name)
