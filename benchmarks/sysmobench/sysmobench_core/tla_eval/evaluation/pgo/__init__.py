"""
System consistency evaluation module for TLA+ specifications.

This module contains evaluators for checking consistency between
generated TLA+ specifications and actual system behavior.
"""

from .trace_validation import PGoTraceValidationEvaluator

__all__ = ['PGoTraceValidationEvaluator']
