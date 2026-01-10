__version__ = "0.1.0"

from courselab_bench.agent import REACTAgent
from courselab_bench.environment import DockerEnvironment
from courselab_bench.model import LiteLLMModel
from courselab_bench.data import load_tasks
from courselab_bench.runner import execute_task, save_trajectory
from courselab_bench.evaluation import evaluate_task, compute_summary

__all__ = [
    "REACTAgent",
    "DockerEnvironment",
    "LiteLLMModel",
    "load_tasks",
    "execute_task",
    "save_trajectory",
    "evaluate_task",
    "compute_summary",
]
