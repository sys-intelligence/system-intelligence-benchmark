"""
Configuration Generation Module

This module handles LLM-based generation of YAML configurations from TLA+ specifications.
"""

from .spec_converter import generate_config_from_tla

__all__ = ['generate_config_from_tla']