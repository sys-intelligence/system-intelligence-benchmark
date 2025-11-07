"""
Model adapters for different LLM providers.

This module provides adapters for various Large Language Model providers,
enabling uniform access to different APIs and local models for TLA+ generation.

Available adapters:
- OpenAIAdapter: OpenAI GPT models (GPT-4, GPT-3.5, etc.)
- AnthropicAdapter: Anthropic Claude models (Claude 3 family)
- GenAIAdapter: Google GenAI models (Gemini family)

Features:
- Automatic retry on 503 Service Unavailable errors (up to 3 retries with 30s delay)
- Uniform interface across all providers
- Comprehensive error handling and logging

Usage:
    from tla_eval.models import get_model_adapter
    
    # Using predefined model configuration
    model = get_model_adapter("openai_gpt4")
    
    # Using custom configuration
    model = get_model_adapter("openai", model_name="claude", temperature=0.2)
    
    # All adapters automatically retry on service unavailable errors
    result = model.generate_tla_specification(source_code, prompt_template)
"""

from .base import (
    ModelAdapter,
    GenerationConfig, 
    GenerationResult,
    ModelError,
    ModelUnavailableError,
    GenerationError,
    RateLimitError
)

from .openai_adapter import OpenAIAdapter
from .anthropic_adapter import AnthropicAdapter
from .genai_adapter import GenAIAdapter
from .factory import ModelFactory, get_model_adapter

__all__ = [
    # Base classes and types
    "ModelAdapter",
    "GenerationConfig", 
    "GenerationResult",
    
    # Exceptions
    "ModelError",
    "ModelUnavailableError", 
    "GenerationError",
    "RateLimitError",
    
    # Adapter implementations
    "OpenAIAdapter",
    "AnthropicAdapter", 
    "GenAIAdapter",
    
    # Factory and utilities
    "ModelFactory",
    "get_model_adapter",
]