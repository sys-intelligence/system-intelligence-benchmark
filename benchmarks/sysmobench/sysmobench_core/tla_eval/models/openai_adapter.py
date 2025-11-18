"""
OpenAI API adapter for TLA+ specification generation.

This module provides integration with OpenAI's GPT models through their API.
Supports GPT-4, GPT-4 Turbo, GPT-3.5 Turbo, and other chat completion models.
"""

import os
import time
from typing import Dict, Any, Optional
import logging

try:
    import openai
    from openai import OpenAI
    OPENAI_AVAILABLE = True
except ImportError:
    OPENAI_AVAILABLE = False

from .base import (
    ModelAdapter, 
    GenerationConfig, 
    GenerationResult,
    ModelError,
    ModelUnavailableError,
    GenerationError,
    RateLimitError
)

logger = logging.getLogger(__name__)


class OpenAIAdapter(ModelAdapter):
    """
    Adapter for OpenAI GPT models via API.
    
    Supports all OpenAI chat completion models including GPT-4, GPT-4 Turbo,
    and GPT-3.5 Turbo.
    
    Configuration parameters:
        - api_key: OpenAI API key (or set OPENAI_API_KEY env var)
        - model_name: Model identifier (e.g., "gpt-4", "gpt-4-turbo")
        - organization: OpenAI organization ID (optional)
        - base_url: Custom API base URL (optional, for Azure OpenAI)
        - max_retries: Maximum number of retry attempts (default: 3)
        - timeout: Request timeout in seconds (default: 60)
    """
    
    # Default model configurations
    MODEL_CONFIGS = {
        "gpt-4": {"max_tokens": 4096, "context_length": 8192},
        "gpt-4-turbo": {"max_tokens": 4096, "context_length": 128000},
        "gpt-4-turbo-preview": {"max_tokens": 4096, "context_length": 128000},
        "gpt-3.5-turbo": {"max_tokens": 4096, "context_length": 16385},
        "gpt-3.5-turbo-16k": {"max_tokens": 4096, "context_length": 16385},
    }
    
    def _setup_model(self):
        """Initialize OpenAI client and validate configuration."""
        if not OPENAI_AVAILABLE:
            raise ModelUnavailableError(
                "OpenAI library not installed. Run: pip install openai"
            )
        
        # Get API key from config or environment
        api_key = self.config.get("api_key") or os.getenv("OPENAI_API_KEY")
        if not api_key:
            raise ModelUnavailableError(
                "OpenAI API key not found. Set OPENAI_API_KEY environment variable "
                "or pass api_key in configuration."
            )
        
        # Initialize OpenAI client
        client_config = {
            "api_key": api_key,
            "max_retries": self.config.get("max_retries", 3),
            "timeout": self.config.get("timeout", 300),  # Increased to 5 minutes for large source files
        }
        
        # Optional organization and base URL (for custom APIs)
        if self.config.get("organization"):
            client_config["organization"] = self.config["organization"]
        if self.config.get("base_url") or self.config.get("url"):
            client_config["base_url"] = self.config.get("base_url") or self.config.get("url")
            
        self.client = OpenAI(**client_config)
        
        # Validate model name
        if self.model_name not in self.MODEL_CONFIGS:
            logger.warning(f"Unknown model {self.model_name}, using default settings")
    
    def _generate_tla_specification_impl(
        self, 
        source_code: str, 
        prompt_template: str,
        generation_config: Optional[GenerationConfig] = None
    ) -> GenerationResult:
        """
        Generate TLA+ specification using OpenAI API.
        
        Args:
            source_code: Source code to convert to TLA+
            prompt_template: Prompt template with {source_code} placeholder
            generation_config: Generation parameters
            
        Returns:
            GenerationResult with generated TLA+ specification
            
        Raises:
            GenerationError: If API call fails
            RateLimitError: If rate limit is exceeded
        """
        if not self.is_available():
            raise ModelUnavailableError("OpenAI adapter is not properly configured")
        
        # Use default config if not provided
        if generation_config is None:
            generation_config = GenerationConfig()
        
        # Format prompt - check if prompt_template already contains the content
        if "{source_code}" in prompt_template:
            prompt = prompt_template.replace("{source_code}", source_code)
        else:
            # Prompt is already formatted, use as-is
            prompt = prompt_template
        
        # Prepare API call parameters
        # Use max_completion_tokens for GPT-5+ models, max_tokens for older models and compatible APIs
        is_gpt5_model = self.model_name.startswith("gpt-5")
        max_tokens_param = "max_completion_tokens" if is_gpt5_model else "max_tokens"
        
        # Use model's configured values if available, otherwise use GenerationConfig value
        model_max_tokens = self.config.get("max_tokens", generation_config.max_tokens)
        model_temperature = self.config.get("temperature", generation_config.temperature)
        model_top_p = self.config.get("top_p", generation_config.top_p)
        
        api_params = {
            "model": self.model_name,
            "messages": [
                {
                    "role": "user", 
                    "content": prompt
                }
            ],
            max_tokens_param: model_max_tokens,
            "temperature": model_temperature,
        }
        
        # GPT-5 doesn't support top_p parameter
        if not is_gpt5_model and model_top_p is not None:
            api_params["top_p"] = model_top_p
        
        # Add optional parameters
        if generation_config.stop_sequences:
            api_params["stop"] = generation_config.stop_sequences
        if generation_config.seed is not None:
            api_params["seed"] = generation_config.seed
        
        # Enable streaming for better timeout handling (but not for GPT-5 due to org verification requirement)
        api_params["stream"] = not is_gpt5_model
        
        # Make API call
        start_time = time.time()
        try:
            if api_params["stream"]:
                logger.info("Starting streaming generation...")
                generated_text = ""
                
                stream = self.client.chat.completions.create(**api_params)
                for chunk in stream:
                    if chunk.choices[0].delta.content is not None:
                        generated_text += chunk.choices[0].delta.content
                        # Optional: Add progress logging every 1000 chars
                        if len(generated_text) % 1000 == 0:
                            logger.debug(f"Generated {len(generated_text)} characters...")
            else:
                logger.info("Starting non-streaming generation...")
                response = self.client.chat.completions.create(**api_params)
                generated_text = response.choices[0].message.content
            
            end_time = time.time()
            
            if not generated_text:
                raise GenerationError("Empty response from OpenAI API")
            
            # For streaming, we don't get usage stats until the end
            # Estimate token usage based on text length (rough approximation)
            estimated_completion_tokens = len(generated_text) // 4  # rough estimate
            
            # Prepare metadata
            metadata = {
                "model": self.model_name,
                "usage": {
                    "prompt_tokens": 0,  # Not available in streaming
                    "completion_tokens": estimated_completion_tokens,
                    "total_tokens": estimated_completion_tokens,
                },
                "latency_seconds": end_time - start_time,
                "finish_reason": "streaming_complete",
                "response_id": f"stream_{int(start_time)}",
                "streaming": True
            }
            
            return GenerationResult(
                generated_text=generated_text,
                metadata=metadata,
                timestamp=end_time,
                success=True
            )
            
        except openai.RateLimitError as e:
            raise RateLimitError(f"OpenAI rate limit exceeded: {e}")
        except openai.APIError as e:
            raise GenerationError(f"OpenAI API error: {e}")
        except Exception as e:
            raise GenerationError(f"Unexpected error during generation: {e}")
    
    def _generate_direct_impl(
        self, 
        complete_prompt: str,
        generation_config: Optional[GenerationConfig] = None
    ) -> GenerationResult:
        """
        Generate content using a complete, pre-formatted prompt.
        
        Args:
            complete_prompt: Complete, ready-to-use prompt text
            generation_config: Generation parameters
            
        Returns:
            GenerationResult containing the generated content
        """
        # Use default config if not provided
        if generation_config is None:
            generation_config = GenerationConfig()
        
        # Prepare API call parameters - use complete_prompt directly
        # Use max_completion_tokens for GPT-5+ models, max_tokens for older models and compatible APIs
        is_gpt5_model = self.model_name.startswith("gpt-5")
        max_tokens_param = "max_completion_tokens" if is_gpt5_model else "max_tokens"
        
        # Use model's configured values if available, otherwise use GenerationConfig value
        model_max_tokens = self.config.get("max_tokens", generation_config.max_tokens)
        model_temperature = self.config.get("temperature", generation_config.temperature)
        model_top_p = self.config.get("top_p", generation_config.top_p)
        
        api_params = {
            "model": self.model_name,
            "messages": [
                {"role": "user", "content": complete_prompt}  # Use complete prompt as-is
            ],
            max_tokens_param: model_max_tokens,
            "temperature": model_temperature,
            "stream": not is_gpt5_model  # GPT-5 requires org verification for streaming
        }
        
        # GPT-5 doesn't support top_p parameter
        if not is_gpt5_model and model_top_p is not None:
            api_params["top_p"] = model_top_p
        
        try:
            start_time = time.time()
            
            if api_params["stream"]:
                logger.info("Starting direct streaming generation...")
                # Make streaming API call
                response = self.client.chat.completions.create(**api_params)
                
                # Collect streaming response
                generated_text = ""
                for chunk in response:
                    # Handle different chunk formats
                    if hasattr(chunk, 'choices') and chunk.choices:
                        choice = chunk.choices[0]
                        if hasattr(choice, 'delta') and hasattr(choice.delta, 'content'):
                            if choice.delta.content is not None:
                                generated_text += choice.delta.content
            else:
                logger.info("Starting direct non-streaming generation...")
                # Make non-streaming API call
                response = self.client.chat.completions.create(**api_params)
                generated_text = response.choices[0].message.content
            
            end_time = time.time()
            
            if not generated_text:
                raise GenerationError("Empty response from OpenAI API")
            
            # Estimate token usage based on text length (rough approximation)
            estimated_completion_tokens = len(generated_text) // 4
            
            # Prepare metadata
            metadata = {
                "model": self.model_name,
                "usage": {
                    "prompt_tokens": 0,  # Not available in streaming
                    "completion_tokens": estimated_completion_tokens,
                    "total_tokens": estimated_completion_tokens,
                },
                "latency_seconds": end_time - start_time,
                "generation_type": "direct",
                "prompt_length": len(complete_prompt),
                "response_length": len(generated_text)
            }
            
            logger.info(f"Direct generation completed in {end_time - start_time:.2f}s")
            logger.info(f"Generated text length: {len(generated_text)} characters")
            
            return GenerationResult(
                generated_text=generated_text,
                metadata=metadata,
                timestamp=end_time,
                success=True
            )
            
        except openai.RateLimitError as e:
            raise RateLimitError(f"OpenAI rate limit exceeded: {e}")
        except openai.APIError as e:
            raise GenerationError(f"OpenAI API error: {e}")
        except Exception as e:
            raise GenerationError(f"Unexpected error during direct generation: {e}")
    
    def is_available(self) -> bool:
        """
        Check if OpenAI adapter is available and properly configured.
        
        Returns:
            True if adapter can be used, False otherwise
        """
        try:
            # Check if OpenAI library is available
            if not OPENAI_AVAILABLE:
                return False
            
            # Check if client is initialized
            if not hasattr(self, 'client'):
                return False
            
            # Check if API key is set
            api_key = self.config.get("api_key") or os.getenv("OPENAI_API_KEY")
            if not api_key:
                return False
            
            return True
            
        except Exception:
            return False
    
    def validate_config(self) -> list[str]:
        """
        Validate OpenAI adapter configuration.
        
        Returns:
            List of validation error messages
        """
        errors = super().validate_config()
        
        # Check OpenAI library
        if not OPENAI_AVAILABLE:
            errors.append("OpenAI library not installed")
        
        # Check API key
        api_key = self.config.get("api_key") or os.getenv("OPENAI_API_KEY")
        if not api_key:
            errors.append("OpenAI API key not found")
        
        # For custom APIs, we don't validate model name format
        if not self.config.get("url") and not self.config.get("base_url"):
            # Only validate OpenAI model names for official OpenAI API
            if self.model_name and not self.model_name.startswith(("gpt-", "text-")):
                errors.append(f"Invalid OpenAI model name: {self.model_name}")
        
        return errors
    
    def get_model_info(self) -> Dict[str, Any]:
        """Get detailed information about the OpenAI model."""
        info = super().get_model_info()
        
        # Add OpenAI-specific information
        model_config = self.MODEL_CONFIGS.get(self.model_name, {})
        info.update({
            "provider": "openai",
            "model_type": "chat_completion",
            "max_tokens": model_config.get("max_tokens", "unknown"),
            "context_length": model_config.get("context_length", "unknown"),
            "api_version": getattr(openai, "__version__", "unknown") if OPENAI_AVAILABLE else "not_installed",
        })
        
        return info
