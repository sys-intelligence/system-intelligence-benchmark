"""
Evaluation modules for TLA+ benchmark framework.

This package contains different dimensions of evaluation:
- Syntax: Compilation checking (can the generated TLA+ be compiled?)
- Semantics: Model checking (can the specification be model-checked?)
- Consistency: Trace validation (does the specification match the system behavior?)
"""

# New structured evaluators
from .syntax.compilation_check import CompilationCheckEvaluator
from .syntax.action_decomposition import ActionDecompositionEvaluator
from .semantics.runtime_check import RuntimeCheckEvaluator
from .semantics.manual_invariant_evaluator import ManualInvariantEvaluator
from .consistency.trace_validation import TraceValidationEvaluator
from .pgo.trace_validation import PGoTraceValidationEvaluator
from .composite.composite_evaluation import CompositeEvaluator

# Base classes and result types
from .base.evaluator import BaseEvaluator
from .base.result_types import (
    EvaluationResult, 
    SyntaxEvaluationResult, 
    SemanticEvaluationResult, 
    ConsistencyEvaluationResult,
    CompositeEvaluationResult
)

# Backward compatibility aliases (deprecated)
# Note: Legacy Phase classes are deprecated, use new structured evaluators instead

__all__ = [
    # New structured evaluators
    "CompilationCheckEvaluator",
    "ActionDecompositionEvaluator",
    "RuntimeCheckEvaluator",
    "ManualInvariantEvaluator", 
    "TraceValidationEvaluator",
    "PGoTraceValidationEvaluator",
    "CompositeEvaluator",
    
    # Base classes and result types
    "BaseEvaluator",
    "EvaluationResult",
    "SyntaxEvaluationResult",
    "SemanticEvaluationResult", 
    "ConsistencyEvaluationResult",
    "CompositeEvaluationResult",
    
    # Legacy compatibility removed - use new structured evaluators
]