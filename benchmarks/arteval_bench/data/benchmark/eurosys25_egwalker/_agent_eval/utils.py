# --- CONSTANTS --- #
from pathlib import Path

HOME = Path.home() / "eurosys25_egwalker"
REPO_DIR = f"{HOME}/egwalker"

REFERENCE_BENCHMARK_FILE = f"{HOME}/_agent_eval/refs/datasets.ref.json"
REFERENCE_RESULTS_FILE = f"{HOME}/_agent_eval/refs/timings.ref.json"
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