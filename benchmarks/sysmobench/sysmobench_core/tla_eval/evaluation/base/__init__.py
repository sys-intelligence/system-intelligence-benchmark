"""
Base evaluation infrastructure.

This module provides common functionality used across all evaluation types.
"""

from .evaluator import BaseEvaluator
from .result_types import EvaluationResult
from .metrics import MetricsCollector
from .metric_registry import (
    MetricRegistry, 
    MetricInfo, 
    get_metric_registry, 
    get_available_metrics,
    get_available_dimensions,
    create_evaluator
)

__all__ = [
    'BaseEvaluator', 
    'EvaluationResult', 
    'MetricsCollector',
    'MetricRegistry',
    'MetricInfo',
    'get_metric_registry',
    'get_available_metrics', 
    'get_available_dimensions',
    'create_evaluator'
]