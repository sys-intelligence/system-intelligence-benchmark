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
from courselab_bench.evaluation.scorer import evaluate_results
from courselab_bench.utils.env_loader import load_env_config


def generate_run_id(agent_name: str, bench_name: str) -> str:
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    return f"{agent_name}_{bench_name}_{timestamp}"


def main():
    parser = argparse.ArgumentParser(
        description="Run benchmark",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--tasks", type=str, required=True, help="Path to tasks.jsonl file")
    parser.add_argument("--agent", type=str, default="react", help="Agent name (default: react)")
    parser.add_argument(
        "--bench", type=str, default="courselab", help="Benchmark name (default: courselab)"
    )
    parser.add_argument(
        "--model",
        type=str,
        default="anthropic/claude-sonnet-4-5-20250929",
        help="Model name for LiteLLM (default: anthropic/claude-sonnet-4-5-20250929)",
    )
    parser.add_argument(
        "--max-steps", type=int, default=50, help="Maximum agent steps (default: 50)"
    )
    parser.add_argument(
        "--max-cost", type=float, default=5.0, help="Maximum cost per task in USD (default: 5.0)"
    )
    parser.add_argument(
        "--output-dir", type=str, default="outputs", help="Base output directory (default: outputs)"
    )

    args = parser.parse_args()
    logger.remove()
    logger.add(sys.stderr, level="INFO", format="<level>{message}</level>", colorize=True)

    load_env_config()
    tasks_file = Path(args.tasks)
    if not tasks_file.exists():
        logger.error(f"Error: Tasks file not found: {tasks_file}")
        sys.exit(1)

    tasks = load_tasks(tasks_file)

    run_id = generate_run_id(args.agent, args.bench)
    output_dir = Path(args.output_dir) / run_id
    output_dir.mkdir(parents=True, exist_ok=True)
    trajectories_dir = output_dir / "trajectories"
    trajectories_dir.mkdir(exist_ok=True)

    logger.info(f"Loaded {len(tasks)} task(s) from {tasks_file.name}")
    logger.info(f"Run ID: {run_id}")

    config = {
        "run_id": run_id,
        "agent": args.agent,
        "benchmark": args.bench,
        "model": args.model,
        "max_steps": args.max_steps,
        "max_cost": args.max_cost,
        "tasks_file": str(tasks_file),
        "num_tasks": len(tasks),
        "timestamp": datetime.now().isoformat(),
    }
    with (output_dir / "config.json").open("w") as f:
        json.dump(config, f, indent=2)

    logger.info("")
    logger.info("=" * 70)
    logger.info("EXECUTION")
    logger.info("=" * 70)

    results_summary = []
    for idx, task in enumerate(tasks, 1):
        logger.info(f"\n[Task {idx}/{len(tasks)}] {task['instance_id']}")

        # Use task timeout if specified, otherwise default to 5 minutes per command
        task_timeout = task.get("timeout_minutes", 30) * 60  # Convert to seconds
        command_timeout = min(task_timeout // 10, 600)  # Max 10 minutes per command

        env = DockerEnvironment(
            image=task["docker_image"], timeout=command_timeout, work_dir="/workspace"
        )
        model = LiteLLMModel(model_name=args.model, temperature=0.0, max_tokens=4096)
        agent = REACTAgent(
            model=model, env=env, config={"max_steps": args.max_steps, "max_cost": args.max_cost}
        )
        try:
            result = execute_task(task, agent, env)
            result_file = output_dir / f"{task['instance_id']}.json"
            with result_file.open("w") as f:
                json.dump(result, f, indent=2)

            trajectory_file = trajectories_dir / f"{task['instance_id']}.jsonl"
            save_trajectory(result["trajectory"], trajectory_file)
            results_summary.append(
                {
                    "instance_id": task["instance_id"],
                    "status": result["agent_status"],
                    "cost": result["model_cost"],
                    "duration": result["duration_seconds"],
                }
            )

        except Exception as e:
            logger.error(f"Error: {e}")
            results_summary.append(
                {"instance_id": task["instance_id"], "status": "error", "error": str(e)}
            )
        finally:
            env.cleanup()

    summary_file = output_dir / "results_summary.json"
    with summary_file.open("w") as f:
        json.dump(
            {
                "run_id": run_id,
                "total_tasks": len(tasks),
                "completed": len([r for r in results_summary if r.get("status") != "error"]),
                "errors": len([r for r in results_summary if r.get("status") == "error"]),
                "total_cost": sum(r.get("cost", 0) for r in results_summary),
                "results": results_summary,
            },
            f,
            indent=2,
        )

    logger.info("")
    logger.info("=" * 70)
    logger.info("EVALUATION")
    logger.info("=" * 70)
    try:
        evaluate_results(output_dir, tasks_file)
    except Exception as e:
        logger.error(f"Evaluation failed: {e}")

    logger.info("")
    logger.info("=" * 70)
    total_cost = sum(r.get("cost", 0) for r in results_summary)
    logger.info(f"Completed {len(tasks)} task(s) | Total cost: ${total_cost:.4f}")
    logger.info(f"Results: {output_dir}")
    logger.info("=" * 70)


if __name__ == "__main__":
    main()
