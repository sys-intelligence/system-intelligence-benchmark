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

import logging

logging.basicConfig(level=logging.INFO, format="[%(levelname)s] %(message)s")
logger = logging.getLogger(__name__)


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
            logger.info(f"\n{'='*70}\nTask: {task_id} ({task_name})\n{'='*70}")

            try:
                sregym_args = argparse.Namespace(
                    agent=agent_name,
                    model=model_name,
                    problem=task_name,
                    use_external_harness=False,
                )

                result = sregym_main(sregym_args)

                output = {
                    "id": task_id,
                    "task_name": task_name,
                    "model_name": model_name,
                    "success": result.success,
                    "final_score": 1.0 if result.success else 0.0,
                    "total_time": result.total_time,
                }
                if result.error:
                    output["error"] = result.error

                scores.append(1.0 if result.success else 0.0)
            except Exception as e:
                logger.error(f"Error: {e}")
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

    logger.info(f"\n{'='*70}\nFinal Score: {avg_score['final_score']:.3f}\n{'='*70}")


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
