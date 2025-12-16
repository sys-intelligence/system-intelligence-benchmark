# --- CONSTANTS --- #
from pathlib import Path

HOME = Path.home() / "sosp23_acto"
REPO_DIR = f"{HOME}/acto"

RESULTS_PATH_TABLES = {
    "table5": f"{REPO_DIR}/table5.txt", 
    "table6": f"{REPO_DIR}/table6.txt",
    "table7": f"{REPO_DIR}/table7.txt",
    "table8": f"{REPO_DIR}/table8.txt"
  }
REFERENCE_PATH_TABLES = {
    "table5": f"{HOME}/_agent_eval/refs/table5.ref.json", 
    "table6": f"{HOME}/_agent_eval/refs/table6.ref.json",
    "table7": f"{HOME}/_agent_eval/refs/table7.ref.json",
    "table8": f"{HOME}/_agent_eval/refs/table8.ref.json"
  }

SIMILARITY_RATIO = 0.75


# --- CUSTOM LOGGER --- #
import logging
import os
from datetime import datetime

os.makedirs('logs', exist_ok=True)

LOG_FORMAT = '%(asctime)s | %(levelname)s | %(name)s | %(message)s'
DATE_FORMAT = '%Y-%m-%d %H:%M:%S'

logger = logging.getLogger("OSDI24-ANVIL-AGENT-EVALUATOR")
logger.setLevel(logging.DEBUG)

console_handler = logging.StreamHandler()
console_handler.setLevel(logging.INFO)
console_handler.setFormatter(logging.Formatter(LOG_FORMAT, datefmt=DATE_FORMAT))

logger.addHandler(console_handler)