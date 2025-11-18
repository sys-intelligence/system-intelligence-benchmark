"""
Anthropic API adapter for TLA+ specification generation.

This module provides integration with Anthropic's Claude models through their API.
Supports Claude 3 (Opus, Sonnet, Haiku) and other models.
"""

import os
import time
from typing import Dict, Any, Optional
import logging

try:
    import anthropic
    from anthropic import Anthropic
    ANTHROPIC_AVAILABLE = True
except ImportError:
    ANTHROPIC_AVAILABLE = False

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


class AnthropicAdapter(ModelAdapter):
    """
    Adapter for Anthropic Claude models via API.
    
    Supports Claude 3 family models (Opus, Sonnet, Haiku) and other 
    Anthropic chat completion models.
    
    Configuration parameters:
        - api_key: Anthropic API key (or set ANTHROPIC_API_KEY env var)
        - model_name: Model identifier (e.g., "claude-3-opus-20240229")
        - max_retries: Maximum number of retry attempts (default: 3)
        - timeout: Request timeout in seconds (default: 60)
    """
    
    # Default model configurations
    MODEL_CONFIGS = {
        "claude-3-opus-20240229": {"max_tokens": 4096, "context_length": 200000},
        "claude-3-sonnet-20240229": {"max_tokens": 4096, "context_length": 200000},
        "claude-3-haiku-20240307": {"max_tokens": 4096, "context_length": 200000},
        "claude-2.1": {"max_tokens": 4096, "context_length": 200000},
        "claude-2.0": {"max_tokens": 4096, "context_length": 100000},
        "claude-instant-1.2": {"max_tokens": 4096, "context_length": 100000},
    }
    
    def _setup_model(self):
        """Initialize Anthropic client and validate configuration."""
        if not ANTHROPIC_AVAILABLE:
            raise ModelUnavailableError(
                "Anthropic library not installed. Run: pip install anthropic"
            )
        
        # Get API key from config or environment
        api_key = self.config.get("api_key") or os.getenv("ANTHROPIC_API_KEY")
        if not api_key:
            raise ModelUnavailableError(
                "Anthropic API key not found. Set ANTHROPIC_API_KEY environment variable "
                "or pass api_key in configuration."
            )
        
        # Initialize Anthropic client
        client_config = {
            "api_key": api_key,
            "max_retries": self.config.get("max_retries", 3),
            "timeout": self.config.get("timeout", 300),  # 5 minutes for large corrections
        }
        
        # Support custom base URL for Anthropic-compatible APIs
        if self.config.get("base_url") or self.config.get("url"):
            client_config["base_url"] = self.config.get("base_url") or self.config.get("url")
            
        self.client = Anthropic(**client_config)
        
        # Validate model name
        if self.model_name not in self.MODEL_CONFIGS:
            logger.warning(f"Unknown Anthropic model {self.model_name}, using default settings")
    
    def _generate_tla_specification_impl(
        self, 
        source_code: str, 
        prompt_template: str,
        generation_config: Optional[GenerationConfig] = None
    ) -> GenerationResult:
        """
        Generate TLA+ specification using Anthropic API.
        
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
            raise ModelUnavailableError("Anthropic adapter is not properly configured")
        
        # Use default config if not provided
        if generation_config is None:
            generation_config = GenerationConfig()
        
        # Format prompt - check if prompt_template already contains the content
        if "{source_code}" in prompt_template:
            user_prompt = prompt_template.replace("{source_code}", source_code)
        else:
            # Prompt is already formatted, use as-is
            user_prompt = prompt_template
        
        # Prepare API call parameters
        api_params = {
            "model": self.model_name,
            "max_tokens": generation_config.max_tokens,
            "temperature": generation_config.temperature,
            "top_p": generation_config.top_p,
            "messages": [
                {
                    "role": "user", 
                    "content": user_prompt
                }
            ]
        }
        
        # Add stop sequences if provided
        if generation_config.stop_sequences:
            api_params["stop_sequences"] = generation_config.stop_sequences
        
        # Make API call with streaming (no stream parameter needed for messages.stream())
        start_time = time.time()
        try:
            logger.info("Starting streaming generation...")
            generated_text = ""
            
            with self.client.messages.stream(**api_params) as stream:
                for text in stream.text_stream:
                    generated_text += text
                    # Optional: Add progress logging every 1000 chars
                    if len(generated_text) % 1000 == 0:
                        logger.debug(f"Generated {len(generated_text)} characters...")
            
            end_time = time.time()
            
            if not generated_text:
                raise GenerationError("Empty text content from Anthropic streaming API")
            
            # Get final message for metadata
            final_message = stream.get_final_message()
            
            # Prepare metadata from streaming response
            metadata = {
                "model": self.model_name,
                "usage": {
                    "input_tokens": final_message.usage.input_tokens,
                    "output_tokens": final_message.usage.output_tokens,
                    "total_tokens": final_message.usage.input_tokens + final_message.usage.output_tokens,
                },
                "latency_seconds": end_time - start_time,
                "stop_reason": final_message.stop_reason,
                "response_id": final_message.id,
                "streaming": True
            }
            
            return GenerationResult(
                generated_text=generated_text,
                metadata=metadata,
                timestamp=end_time,
                success=True
            )
            
        except anthropic.RateLimitError as e:
            raise RateLimitError(f"Anthropic rate limit exceeded: {e}")
        except anthropic.APIError as e:
            raise GenerationError(f"Anthropic API error: {e}")
        except Exception as e:
            logger.error(f"Streaming generation failed: {e}")
            raise GenerationError(f"Unexpected error during streaming generation: {e}")
    
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
        api_params = {
            "model": self.model_name,
            "max_tokens": generation_config.max_tokens,
            "temperature": generation_config.temperature,
            "top_p": generation_config.top_p,
            "messages": [
                {
                    "role": "user", 
                    "content": complete_prompt  # Use the complete prompt as-is
                }
            ]
        }
        
        # Filter out None values
        api_params = {k: v for k, v in api_params.items() if v is not None}
        
        try:
            logger.info("Starting direct generation...")
            start_time = time.time()
            
            # Make API call with streaming
            response = self.client.messages.create(**api_params, stream=True)
            
            # Collect streaming response
            generated_text = ""
            for chunk in response:
                if hasattr(chunk, 'delta') and hasattr(chunk.delta, 'text'):
                    generated_text += chunk.delta.text
            
            end_time = time.time()
            
            # Log successful generation
            logger.info(f"Direct generation completed in {end_time - start_time:.2f}s")
            logger.info(f"Generated text length: {len(generated_text)} characters")
            
            return GenerationResult(
                generated_text=generated_text,
                metadata={
                    "model": self.model_name,
                    "latency_seconds": end_time - start_time,
                    "generation_type": "direct",
                    "prompt_length": len(complete_prompt),
                    "response_length": len(generated_text)
                },
                timestamp=end_time,
                success=True
            )
            
        except anthropic.RateLimitError as e:
            raise RateLimitError(f"Anthropic rate limit exceeded: {e}")
        except anthropic.APIError as e:
            raise GenerationError(f"Anthropic API error: {e}")
        except Exception as e:
            logger.error(f"Direct generation failed: {e}")
            raise GenerationError(f"Unexpected error during direct generation: {e}")
    
    def is_available(self) -> bool:
        """
        Check if Anthropic adapter is available and properly configured.
        
        Returns:
            True if adapter can be used, False otherwise
        """
        try:
            # Check if Anthropic library is available
            if not ANTHROPIC_AVAILABLE:
                return False
            
            # Check if client is initialized
            if not hasattr(self, 'client'):
                return False
            
            # Check if API key is set
            api_key = self.config.get("api_key") or os.getenv("ANTHROPIC_API_KEY")
            if not api_key:
                return False
            
            return True
            
        except Exception:
            return False
    
    def validate_config(self) -> list[str]:
        """
        Validate Anthropic adapter configuration.
        
        Returns:
            List of validation error messages
        """
        errors = super().validate_config()
        
        # Check Anthropic library
        if not ANTHROPIC_AVAILABLE:
            errors.append("Anthropic library not installed")
        
        # Check API key
        api_key = self.config.get("api_key") or os.getenv("ANTHROPIC_API_KEY")
        if not api_key:
            errors.append("Anthropic API key not found")
        
        # Check model name format
        if self.model_name and not self.model_name.startswith("claude"):
            errors.append(f"Invalid Anthropic model name: {self.model_name}")
        
        return errors
    
    def get_model_info(self) -> Dict[str, Any]:
        """Get detailed information about the Anthropic model."""
        info = super().get_model_info()
        
        # Add Anthropic-specific information
        model_config = self.MODEL_CONFIGS.get(self.model_name, {})
        info.update({
            "provider": "anthropic",
            "model_type": "chat_completion",
            "max_tokens": model_config.get("max_tokens", "unknown"),
            "context_length": model_config.get("context_length", "unknown"),
            "api_version": getattr(anthropic, "__version__", "unknown") if ANTHROPIC_AVAILABLE else "not_installed",
        })
        
        return info
