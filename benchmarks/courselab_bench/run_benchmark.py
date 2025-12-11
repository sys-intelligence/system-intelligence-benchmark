#!/usr/bin/env python3
import sys
import json
import argparse
from pathlib import Path
from datetime import datetime
from loguru import logger

sys.path.insert(0, str(Path(__file__).parent))
from courselab_bench import (
    load_tasks,
    DockerEnvironment,
    LiteLLMModel,
    REACTAgent,
    execute_task,
    save_trajectory,
)
from courselab_bench.evaluation.evaluator import evaluate_task, compute_summary
from courselab_bench.utils.env_loader import load_env_config


def main():
    parser = argparse.ArgumentParser(description="Run benchmark")
    parser.add_argument(
        "--tasks",
        type=str,
        default="data/tasks.jsonl",
        help="Path to tasks JSONL file (default: data/tasks.jsonl)",
    )
    parser.add_argument("--model", type=str, default="anthropic/claude-sonnet-4-5-20250929")
    parser.add_argument("--max-steps", type=int, default=50)
    parser.add_argument("--max-cost", type=float, default=5.0)
    parser.add_argument("--output-dir", type=str, default="outputs")

    args = parser.parse_args()
    logger.remove()
    logger.add(sys.stderr, level="INFO", format="<level>{message}</level>", colorize=True)

    load_env_config()
    tasks_file = Path(args.tasks)
    if not tasks_file.exists():
        logger.error(f"Error: Tasks file not found: {tasks_file}")
        logger.error("Run 'python prepare_dataset.py' first to generate tasks.jsonl")
        sys.exit(1)

    tasks = load_tasks(tasks_file)
    if not tasks:
        logger.error("No tasks found")
        sys.exit(1)

    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    output_dir = Path(args.output_dir) / f"run_{timestamp}"
    output_dir.mkdir(parents=True, exist_ok=True)
    (output_dir / "trajectories").mkdir(exist_ok=True)

    logger.info(f"Loaded {len(tasks)} task(s)")
    logger.info(f"Output: {output_dir}")

    results = []
    for idx, task in enumerate(tasks, 1):
        logger.info(f"\n[{idx}/{len(tasks)}] {task['instance_id']}")

        env = DockerEnvironment(
            image=task["docker_image"],
            timeout=task.get("timeout_minutes", 30) * 60,
            work_dir="/workspace",
        )
        model = LiteLLMModel(model_name=args.model, temperature=0.0, max_tokens=4096)
        agent = REACTAgent(
            model=model, env=env, config={"max_steps": args.max_steps, "max_cost": args.max_cost}
        )

        try:
            result = execute_task(task, agent, env)
            result["course_id"] = task["course_id"]
            result["passed"] = evaluate_task(result)

            trajectory = result.pop("trajectory", [])
            traj_file = output_dir / "trajectories" / f"{task['instance_id']}.jsonl"
            save_trajectory(trajectory, traj_file)

            results.append(result)

            status = "✓" if result["passed"] else "✗"
            logger.info(f"{status} {result['agent_status']} | ${result['model_cost']:.4f}")

        except Exception as e:
            logger.error(f"Error: {e}")
            results.append(
                {
                    "instance_id": task["instance_id"],
                    "course_id": task["course_id"],
                    "passed": False,
                    "agent_status": "error",
                    "error": str(e),
                }
            )
        finally:
            env.cleanup()

    summary = compute_summary(results)
    output = {
        "config": {
            "model": args.model,
            "max_steps": args.max_steps,
            "max_cost": args.max_cost,
            "timestamp": datetime.now().isoformat(),
        },
        "summary": summary,
        "results": results,
    }

    with (output_dir / "results.json").open("w") as f:
        json.dump(output, f, indent=2)

    logger.info("\n" + "=" * 70)
    logger.info(
        f"Pass rate: {summary['passed']}/{summary['total']} ({summary['success_rate']:.1%})"
    )
    logger.info(f"Total cost: ${summary['total_cost']:.4f}")
    logger.info(f"Results: {output_dir}")
    logger.info("=" * 70)


if __name__ == "__main__":
    main()
