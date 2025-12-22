"""
Run TopoSense-Bench Evaluation.
"""

import argparse
import json
import os
import sys
from datetime import datetime

import pandas as pd
from datasets import load_dataset
from tqdm import tqdm

# Add parent directory to path to import the shared SDK
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../../../")))

from loguru import logger
from sdk.executor import SimpleExecutor
from sdk.utils import set_llm_endpoint_from_config
from evaluator import TopoSenseEvaluator
from topology_loader import TopologyManager

# System Prompt
SYSTEM_PROMPT_TEMPLATE = """You are an intelligent sensor scheduling agent (IoT-Brain).
You will be provided with a specific TOPOLOGICAL MAP of a building floor and a USER QUERY.

Your Task:
1. Analyze the user's intent and location description in the query.
2. Search the provided MAP DATA to find the specific sensor node that best answers the query (e.g., covers the mentioned area).
3. Return the exact 'name' of the sensor node.

Output Format:
Please return a JSON object:
```json
{
    "answer": "sensor_name_here",
    "explanation": "Brief reasoning based on map tags"
}
```
Output ONLY the JSON code block.
"""
def compute_summary(results_df):
    """Compute summary statistics."""
    total_questions = len(results_df)
    answered = len(results_df[results_df["status"] != "error"])
    correct = len(results_df[results_df["status"] == "correct"])
    incorrect = len(results_df[results_df["status"] == "incorrect"])

    summary = {
        "overall": {
            "total_questions": total_questions,
            "answered": answered,
            "correct": correct,
            "incorrect": incorrect,
            "accuracy": round(correct / answered, 4) if answered > 0 else 0,
        },
        "by_category": []
    }

    if "category" in results_df.columns:
        for category in results_df["category"].unique():
            cat_df = results_df[results_df["category"] == category]
            cat_total = len(cat_df)
            cat_correct = len(cat_df[cat_df["status"] == "correct"])
            
            summary["by_category"].append({
                "category": category,
                "total": cat_total,
                "correct": cat_correct,
                "accuracy": round(cat_correct / cat_total, 4) if cat_total > 0 else 0
            })
    return summary

def main(model_name, output_dir):
    """Main evaluation loop."""
    # 1. Setup Configuration Path
    current_dir = os.path.dirname(os.path.abspath(__file__))
    local_config = os.path.abspath(os.path.join(current_dir, "../env.toml"))
    global_config = os.path.abspath(os.path.join(current_dir, "../../env.toml"))

    if os.path.exists(local_config):
        config_path = local_config
    elif os.path.exists(global_config):
        config_path = global_config
    else:
        config_path = local_config 

    if os.path.exists(config_path):
        logger.info(f"Loading config from: {config_path}")
        set_llm_endpoint_from_config(config_path)
    else:
        logger.warning(f"Config file not found at {config_path}, relying on environment variables.")

    # Initialize components
    try:
        executor = SimpleExecutor(model_name, SYSTEM_PROMPT_TEMPLATE)
    except Exception as e:
        logger.error(f"Failed to initialize Executor: {e}")
        return

    evaluator = TopoSenseEvaluator()
    topo_manager = TopologyManager()

    # 2. Load Queries
    logger.info("📥 Loading Queries from Hugging Face...")
    try:
        dataset = load_dataset("IoT-Brain/TopoSense-Bench", "queries", split="train")
        logger.info(f"✅ Loaded {len(dataset)} queries.")
    except Exception as e:
        logger.error(f"Failed to load dataset: {e}")
        return

    minimal_results = []
    detailed_results = []

    # 3. Evaluation Loop
    try:
        for item in tqdm(dataset):
            query = item['query']
            ground_truth = item['answer']
            category = item['category']

            # Context Retrieval
            context_map = topo_manager.retrieve_context(query)

            if context_map:
                user_prompt = f"{context_map}\n\n[User Query]\n{query}"
            else:
                user_prompt = (
                    f"[Map Data]\n(No specific map retrieved, relying on common knowledge)\n\n"
                    f"[User Query]\n{query}"
                )

            try:
                response_str = executor.run(user_prompt, lang='json')
                
                try:
                    response_json = json.loads(response_str)
                    llm_answer = response_json.get("answer", "")
                    llm_explanation = response_json.get("explanation", "")
                except json.JSONDecodeError:
                    llm_answer = response_str
                    llm_explanation = "Failed to parse JSON"
                    response_json = {"answer": response_str}

                # Evaluate Answer
                eval_res = evaluator.eval(response_json, ground_truth)

                # Construct Result Objects
                minimal_result = {
                    "category": category,
                    "query": query,
                    "ground_truth": ground_truth,
                    "llm_answer": llm_answer,
                    "status": eval_res["status"],
                    "score": eval_res["score"]
                }
                
                detailed_result = {
                    **minimal_result,
                    "llm_explanation": llm_explanation,
                    "retrieved_context": bool(context_map),
                    "full_prompt": user_prompt,
                    "raw_response": response_str
                }

                minimal_results.append(minimal_result)
                detailed_results.append(detailed_result)

            except Exception as e:
                logger.error(f"Error processing query: {e}")
                error_result = {
                    "category": category,
                    "query": query,
                    "status": "error",
                    "error": str(e)
                }
                minimal_results.append(error_result)
                detailed_results.append(error_result)
                
    except KeyboardInterrupt:
        logger.warning("Evaluation interrupted by user. Saving partial results...")

    # 4. Save Results
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    # 4.1 Save Detailed Results (JSONL)
    with open(os.path.join(output_dir, "results_detailed.jsonl"), "w", encoding="utf-8") as f:
        for res in detailed_results:
            f.write(json.dumps(res, ensure_ascii=False) + "\n")

    # 4.2 Save Minimal Results (JSONL)
    with open(os.path.join(output_dir, "results.jsonl"), "w", encoding="utf-8") as f:
        for res in minimal_results:
            f.write(json.dumps(res, ensure_ascii=False) + "\n")

    # 4.3 Generate Summary
    results_df = pd.DataFrame(minimal_results)
    if not results_df.empty:
        summary = compute_summary(results_df)
        summary["model"] = model_name
        summary["timestamp"] = datetime.now().isoformat()

        with open(os.path.join(output_dir, "summary.json"), "w", encoding="utf-8") as f:
            json.dump(summary, f, indent=2, ensure_ascii=False)

        logger.info(f"✅ Eval Done. Accuracy: {summary['overall']['accuracy']:.2%}")
        logger.info(f"📂 Results saved to: {output_dir}")
    else:
        logger.warning("No results to save.")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="TopoSense-Bench Evaluation")
    parser.add_argument("-m", "--model_name", default="gpt-4o", help="Model name to evaluate")
    parser.add_argument("-o", "--output_dir", default=None, help="Directory to save results")
    args = parser.parse_args()

    if args.output_dir is None:
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        safe_model_name = args.model_name.replace('/', '_')
        args.output_dir = f"./outputs/toposense_{safe_model_name}_{timestamp}"

    main(args.model_name, args.output_dir)