"""
Syntax-level evaluation module for TLA+ specifications.

This module contains evaluators for checking the syntactic correctness
of generated TLA+ specifications.
"""

from .compilation_check import CompilationCheckEvaluator

__all__ = ['CompilationCheckEvaluator']