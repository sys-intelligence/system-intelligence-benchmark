#!/usr/bin/env python3

# --- CONSTANTS --- #
from pathlib import Path

HOME = Path.home()
REPO_DIR = HOME / "sosp24_wasabi"/ "wasabi"
BENCH_DIR = HOME / "sosp24_wasabi" / "benchmarks"
RESULTS_ROOT_DIR = REPO_DIR / "results"
GROUND_TRUTH_FILE = REPO_DIR / "bugs_ground_truth.txt"
SIMILARITY_RATIO = 0.75


# --- CUSTOM LOGGER --- #
import logging
import os
from datetime import datetime

os.makedirs('logs', exist_ok=True)

LOG_FORMAT = '%(asctime)s | %(levelname)s | %(name)s | %(message)s'
DATE_FORMAT = '%Y-%m-%d %H:%M:%S'

logger = logging.getLogger("WASABI-AGENT-EVALUATOR")
logger.setLevel(logging.DEBUG)

console_handler = logging.StreamHandler()
console_handler.setLevel(logging.INFO)
console_handler.setFormatter(logging.Formatter(LOG_FORMAT, datefmt=DATE_FORMAT))

logger.addHandler(console_handler)