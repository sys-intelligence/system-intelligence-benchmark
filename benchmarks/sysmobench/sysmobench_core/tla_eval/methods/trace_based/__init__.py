"""
Trace-based TLA+ generation method.

This module implements a trace-based approach to TLA+ specification generation
that includes automatic error detection and correction, without referencing the codebase at all.
This is intended to evaluate how PGo/compiled implementations may fare since their codebase structure is less legible.
"""

from .method import TraceBasedMethod 

__all__ = ['TraceBasedMethod']