# --- CONSTANTS --- #
from pathlib import Path

HOME = Path.home() / "osdi24_anvil"
REPO_DIRS = {"acto": f"{HOME}/acto", "anvil": f"{HOME}/anvil"}
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