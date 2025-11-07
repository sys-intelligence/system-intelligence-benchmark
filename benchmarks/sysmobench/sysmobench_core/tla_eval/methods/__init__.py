"""
TLA+ generation methods.

This module contains different approaches for generating TLA+ specifications
from source code, including direct LLM calls and agent-based methods.
"""

from .base import TLAGenerationMethod
from .direct_call import DirectCallMethod
from .agent_based import AgentBasedMethod
from .trace_based import TraceBasedMethod

# Method registry
_METHODS = {
    "direct_call": DirectCallMethod,
    "agent_based": AgentBasedMethod,
    "trace_based": TraceBasedMethod,
}

def get_method(method_name: str) -> TLAGenerationMethod:
    """Get a method instance by name."""
    if method_name not in _METHODS:
        available = list(_METHODS.keys())
        raise ValueError(f"Unknown method '{method_name}'. Available: {available}")
    
    method_class = _METHODS[method_name]
    return method_class()

def list_available_methods() -> list:
    """List all available method names."""
    return list(_METHODS.keys())

__all__ = [
    "TLAGenerationMethod",
    "DirectCallMethod",
    "AgentBasedMethod",
    "TraceBasedMethod",
    "get_method",
    "list_available_methods",
]