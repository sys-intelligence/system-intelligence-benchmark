"""
Specification Processing Module

This module handles the processing and conversion of TLA+ specifications:
- LLM-based configuration generation from TLA+ specs
- Static analysis conversion to trace validation format  
- Trace format conversion for verification
"""

from .spec_converter import SpecTraceGenerator, generate_config_from_tla
from .config_generation import generate_config_from_tla as config_gen

__all__ = ['SpecTraceGenerator', 'generate_config_from_tla']