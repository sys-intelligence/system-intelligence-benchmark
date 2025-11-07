"""
Benchmark tasks with source code from real systems.

This module provides test cases based on real distributed and concurrent systems
like etcd, raft, etc.
"""

from .loader import TaskLoader, load_task

__all__ = [
    "TaskLoader", 
    "load_task"
]