"""
Specification Processing Module

This module handles the processing and conversion of TLA+ specifications:
- LLM-based configuration generation from TLA+ specs
- Static analysis conversion to trace validation format
- Trace format conversion for verification
- Alloy trace processing and conversion
"""

from .spec_converter import SpecTraceGenerator, generate_config_from_tla
from .config_generation import generate_config_from_tla as config_gen
from .alloy_trace_processor import AlloyTraceConverter, create_alloy_trace_converter

__all__ = [
    'SpecTraceGenerator',
    'generate_config_from_tla',
    'AlloyTraceConverter',
    'create_alloy_trace_converter'
]