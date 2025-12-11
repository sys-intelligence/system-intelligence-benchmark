"""Evaluator for TopoSense Benchmark."""

import re
import ast
from loguru import logger


class TopoSenseEvaluator:
    """Evaluator class for Semantic-Spatial Sensor Scheduling tasks."""

    def __init__(self):
        pass

    def parse_node_info(self, text):
        """
        Parses the Node string representation to extract the critical 'name' tag.

        Input format example:
        "Node(223, 307, Tags: {'man_made': 'surveillance', 'name': 'camera_1'})"

        Args:
            text (str): The raw ground truth string from the dataset.

        Returns:
            str: The extracted sensor name (e.g., "camera_1") or the original text if parsing fails.
        """
        try:
            # 1. Attempt to extract the Tags dictionary part using regex
            tags_match = re.search(r"Tags:\s*(\{.*?\})", text)
            if tags_match:
                tags_str = tags_match.group(1)
                # Safely evaluate the string as a Python dictionary
                tags = ast.literal_eval(tags_str)
                # Return the 'name' tag converted to lowercase
                return tags.get('name', '').lower()

            # 2. Fallback: If it's a pure ID format or regex fails, return normalized text
            return text.strip().lower()
        except Exception:
            return text.strip().lower()

    def eval(self, llm_response_json, ground_truth_str):
        """
        Evaluate the LLM's response against the ground truth.

        Args:
            llm_response_json (dict): The JSON output from the LLM.
                                      Expected format: {"answer": "...", "explanation": "..."}
            ground_truth_str (str): The raw answer string from the dataset.

        Returns:
            dict: Evaluation result containing status, score, and parsed ground truth.
        """
        # 1. Extract the core answer from the LLM response
        llm_answer = str(llm_response_json.get("answer", "")).lower()

        # 2. Parse the unique identifier (Target Name) from the Ground Truth
        gt_target_name = self.parse_node_info(ground_truth_str)

        # 3. Evaluation Logic
        # Requirement: The LLM's answer must contain the core identifier of the GT.
        # Example:
        #   GT: "fire_fighting_access_1_camera_1"
        #   LLM: "I suggest using fire_fighting_access_1_camera_1" -> Correct

        # Normalize strings by replacing underscores and hyphens with spaces for robust matching
        clean_llm = llm_answer.replace("_", " ").replace("-", " ")
        clean_gt = gt_target_name.replace("_", " ").replace("-", " ")

        # Perform containment check
        is_correct = clean_gt in clean_llm

        return {
            "status": "correct" if is_correct else "incorrect",
            "score": 1 if is_correct else 0,
            "parsed_gt": gt_target_name
        }