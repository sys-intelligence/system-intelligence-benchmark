"""
Model adapter factory for creating model instances.

This module provides utilities for dynamically creating model adapters
based on configuration, supporting both predefined and custom adapters.
"""

from typing import Dict, Any, Type, Optional
import logging

from .base import ModelAdapter, ModelUnavailableError
from .openai_adapter import OpenAIAdapter
from .anthropic_adapter import AnthropicAdapter
from .genai_adapter import GenAIAdapter
from .exist_spec_adapter import ExistSpecAdapter

logger = logging.getLogger(__name__)


class ModelFactory:
    """Factory class for creating model adapters."""
    
    # Registry of available model adapters
    _ADAPTERS: Dict[str, Type[ModelAdapter]] = {
        "openai": OpenAIAdapter,
        "anthropic": AnthropicAdapter,
        "genai": GenAIAdapter,
        "google_genai": GenAIAdapter,  # Alternative name
        "exist_spec": ExistSpecAdapter,
    }
    
    # Predefined model configurations
    _PREDEFINED_MODELS = {
        # OpenAI models
        "openai_gpt4": {
            "provider": "openai",
            "model_name": "claude",
            "temperature": 0.1,
        },
        "openai_gpt4_turbo": {
            "provider": "openai", 
            "model_name": "gpt-4-turbo",
            "temperature": 0.1,
        },
        "openai_gpt35_turbo": {
            "provider": "openai",
            "model_name": "gpt-3.5-turbo",
            "temperature": 0.1,
        },
        
        # Anthropic models
        "anthropic_claude3_opus": {
            "provider": "anthropic",
            "model_name": "claude-3-opus-20240229", 
            "temperature": 0.1,
        },
        "anthropic_claude3_sonnet": {
            "provider": "anthropic",
            "model_name": "claude-3-sonnet-20240229",
            "temperature": 0.1,
        },
        "anthropic_claude3_haiku": {
            "provider": "anthropic",
            "model_name": "claude-3-haiku-20240307",
            "temperature": 0.1,
        },
        
        # Google GenAI models
        "genai_gemini_2_5_flash": {
            "provider": "genai",
            "model_name": "gemini-2.5-flash",
            "temperature": 0.1,
            "thinking_budget": 0,
        },
        "genai_gemini_1_5_pro": {
            "provider": "genai", 
            "model_name": "gemini-1.5-pro",
            "temperature": 0.1,
            "thinking_budget": 0,
        },
        "genai_gemini_1_5_flash": {
            "provider": "genai",
            "model_name": "gemini-1.5-flash",
            "temperature": 0.1,
            "thinking_budget": 0,
        },
        "genai_gemini_pro": {
            "provider": "genai",
            "model_name": "gemini-pro",
            "temperature": 0.1,
            "thinking_budget": 0,
        },
        
        # Special adapters
        "with_exist_spec": {
            "provider": "exist_spec",
            "model_name": "with_exist_spec",
            "temperature": 0.0,
        },
    }
    
    @classmethod
    def create_adapter(
        cls, 
        model_identifier: str, 
        **config_overrides
    ) -> ModelAdapter:
        """
        Create a model adapter instance.
        
        Args:
            model_identifier: Either a predefined model name (e.g., "openai_gpt4")
                            or provider name (e.g., "openai") with model_name in config
            **config_overrides: Additional configuration parameters
            
        Returns:
            Initialized model adapter instance
            
        Raises:
            ModelUnavailableError: If model cannot be created
            
        Examples:
            # Using predefined model
            adapter = ModelFactory.create_adapter("openai_gpt4")
            
            # Using provider with custom config
            adapter = ModelFactory.create_adapter(
                "openai", 
                model_name="gpt-4-turbo",
                temperature=0.2
            )
        """
        # Check if it's a predefined model
        if model_identifier in cls._PREDEFINED_MODELS:
            config = cls._PREDEFINED_MODELS[model_identifier].copy()
            config.update(config_overrides)
            provider = config.pop("provider")
            model_name = config.pop("model_name")
        else:
            # Treat as provider name
            provider = model_identifier
            config = config_overrides.copy()
            model_name = config.pop("model_name", None)
            
            if not model_name:
                raise ModelUnavailableError(
                    f"model_name required when using provider '{provider}'"
                )
        
        # Get adapter class - for unknown providers, try OpenAI-compatible API
        if provider not in cls._ADAPTERS:
            logger.info(f"Unknown provider '{provider}', trying OpenAI-compatible adapter")
            adapter_class = OpenAIAdapter
        else:
            adapter_class = cls._ADAPTERS[provider]
        
        try:
            # Create adapter instance
            adapter = adapter_class(model_name=model_name, **config)
            
            # Validate configuration
            validation_errors = adapter.validate_config()
            if validation_errors:
                raise ModelUnavailableError(
                    f"Configuration validation failed: {', '.join(validation_errors)}"
                )
            
            return adapter
            
        except Exception as e:
            logger.error(f"Failed to create adapter for {model_identifier}: {e}")
            raise ModelUnavailableError(f"Failed to create model adapter: {e}")
    
    @classmethod
    def register_adapter(cls, provider: str, adapter_class: Type[ModelAdapter]):
        """
        Register a custom model adapter.
        
        Args:
            provider: Provider name (e.g., "custom_provider")
            adapter_class: ModelAdapter subclass
            
        Example:
            class MyCustomAdapter(ModelAdapter):
                # Implementation here
                pass
                
            ModelFactory.register_adapter("my_provider", MyCustomAdapter)
        """
        if not issubclass(adapter_class, ModelAdapter):
            raise ValueError("adapter_class must be a subclass of ModelAdapter")
        
        cls._ADAPTERS[provider] = adapter_class
        logger.info(f"Registered custom adapter for provider '{provider}'")
    
    @classmethod
    def list_available_models(cls) -> Dict[str, Any]:
        """
        List all available models and providers.
        
        Returns:
            Dictionary with predefined models and available providers
        """
        return {
            "predefined_models": list(cls._PREDEFINED_MODELS.keys()),
            "providers": list(cls._ADAPTERS.keys()),
            "predefined_configs": cls._PREDEFINED_MODELS.copy()
        }
    
    @classmethod
    def get_model_config(cls, model_identifier: str) -> Dict[str, Any]:
        """
        Get configuration for a predefined model.
        
        Args:
            model_identifier: Predefined model name
            
        Returns:
            Model configuration dictionary
            
        Raises:
            KeyError: If model is not predefined
        """
        if model_identifier not in cls._PREDEFINED_MODELS:
            raise KeyError(f"Model '{model_identifier}' not found in predefined models")
        
        return cls._PREDEFINED_MODELS[model_identifier].copy()


# Convenience function for creating adapters
def get_model_adapter(model_identifier: str, **config) -> ModelAdapter:
    """
    Convenience function to create a model adapter.
    
    Args:
        model_identifier: Model identifier or provider name
        **config: Additional configuration parameters
        
    Returns:
        Initialized model adapter
    """
    return ModelFactory.create_adapter(model_identifier, **config)