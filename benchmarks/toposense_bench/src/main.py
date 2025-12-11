"""
Run TopoSense-Bench Evaluation.

This script executes the benchmark by loading queries from Hugging Face,
retrieving relevant topological contexts, and evaluating the LLM's response.
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

# System Prompt emphasizes reasoning based on the provided Map Data
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
Output ONLY the JSON code block.
"""

def main(model_name, output_dir):
    """
    Main evaluation loop.
    Args:
        model_name (str): The name of the LLM to evaluate.
        output_dir (str): Directory to save results.
    """

    # 1. Setup Configuration Path
    # Prioritize finding env.toml in the current benchmark directory (src/../env.toml)
    current_dir = os.path.dirname(os.path.abspath(__file__))
    local_config = os.path.abspath(os.path.join(current_dir, "../env.toml"))
    global_config = os.path.abspath(os.path.join(current_dir, "../../env.toml"))

    if os.path.exists(local_config):
        config_path = local_config
    elif os.path.exists(global_config):
        config_path = global_config
    else:
        config_path = local_config  # Default to local path for clearer error messages

    if os.path.exists(config_path):
        logger.info(f"Loading config from: {config_path}")
        set_llm_endpoint_from_config(config_path)
    else:
        logger.warning(f"⚠️ Config file not found at {config_path}, relying on environment variables.")

    # Initialize components
    executor = SimpleExecutor(model_name, SYSTEM_PROMPT_TEMPLATE)
    evaluator = TopoSenseEvaluator()
    topo_manager = TopologyManager()  # Handles loading and indexing of topology data

    # 2. Load Queries from Hugging Face
    logger.info("📥 Loading Queries...")
    # Hugging Face defaults uploaded JSONL files to the 'train' split if not specified in YAML
    dataset = load_dataset("IoT-Brain-Project/TopoSense-Bench", "queries", split="train")

    results = []

    # 3. Evaluation Loop
    for item in tqdm(dataset):
        query = item['query']
        ground_truth = item['answer']
        category = item['category']

        # --- Context Retrieval ---
        # Retrieve the relevant map/floor plan based on the query
        context_map = topo_manager.retrieve_context(query)

        if context_map:
            # Oracle Context Mode: Provide the specific map data
            user_prompt = f"{context_map}\n\n[User Query]\n{query}"
        else:
            # Zero-context Fallback: If retrieval fails (e.g., complex cross-floor queries)
            user_prompt = (
                f"[Map Data]\n(No specific map retrieved, please rely on common knowledge if possible)\n\n"
                f"[User Query]\n{query}"
            )

        try:
            # Call LLM using SimpleExecutor (which extracts JSON from markdown blocks)
            response_str = executor.run(user_prompt, lang='json')

            # Parse JSON Response
            try:
                response_json = json.loads(response_str)
                llm_answer = response_json.get("answer", "")
            except json.JSONDecodeError:
                # Fallback if response is not valid JSON
                llm_answer = response_str
                response_json = {"answer": response_str}

            # Evaluate Answer
            eval_res = evaluator.eval(response_json, ground_truth)

            results.append({
                "category": category,
                "query": query,
                "ground_truth": ground_truth,
                "retrieved_context": bool(context_map),  # Track retrieval success
                "llm_answer": llm_answer,
                "status": eval_res["status"],
                "score": eval_res["score"]
            })

        except Exception as e:
            logger.error(f"Error processing query: {e}")
            results.append({
                "query": query,
                "status": "error",
                "error": str(e)
            })

    # 4. Save Results & Summarize
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)

    df = pd.DataFrame(results)
    df.to_json(
        os.path.join(output_dir, "results.jsonl"),
        orient="records",
        lines=True,
        force_ascii=False
    )

    # Calculate overall accuracy
    if len(df) > 0:
        acc = df[df["status"] == "correct"].shape[0] / len(df)
        retrieval_rate = df["retrieved_context"].mean() if "retrieved_context" in df.columns else 0
    else:
        acc = 0
        retrieval_rate = 0

    logger.info(f"✅ Eval Done. Accuracy: {acc:.2%}")
    logger.info(f"   Context Retrieval Rate: {retrieval_rate:.2%}")

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