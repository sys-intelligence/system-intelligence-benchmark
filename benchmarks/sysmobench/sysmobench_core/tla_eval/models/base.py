"""
Base adapter interface for LLM models.

This module defines the abstract base class that all model adapters must implement.
It ensures compatibility between different model types (API-based, local, etc.).
"""

from abc import ABC, abstractmethod
from typing import Dict, Any, Optional, List, Callable
from dataclasses import dataclass
import time
import logging


@dataclass
class GenerationConfig:
    """Configuration for text generation parameters."""
    max_tokens: int = 32000
    temperature: float = 0.1
    top_p: float = 0.9
    stop_sequences: Optional[List[str]] = None
    seed: Optional[int] = None
    use_json_mode: bool = False


@dataclass
class GenerationResult:
    """Result of text generation from a model."""
    generated_text: str
    metadata: Dict[str, Any]  # Model-specific metadata (tokens used, latency, etc.)
    timestamp: float
    success: bool = True
    error_message: Optional[str] = None

    def __post_init__(self):
        if self.timestamp == 0:
            self.timestamp = time.time()


logger = logging.getLogger(__name__)


class ModelAdapter(ABC):
    """
    Abstract base class for all model adapters.
    
    This interface ensures that all model types (API-based, local, etc.) 
    can be used interchangeably in the benchmark framework.
    """
    
    def __init__(self, model_name: str, **kwargs):
        """
        Initialize the model adapter.
        
        Args:
            model_name: Name/identifier of the model
            **kwargs: Model-specific configuration parameters
        """
        self.model_name = model_name
        self.config = kwargs
        self._setup_model()
    
    def _retry_on_service_unavailable(self, func: Callable, *args, **kwargs):
        """
        Retry wrapper for handling server errors (500, 503, etc.).
        
        Args:
            func: Function to retry
            *args: Arguments to pass to the function
            **kwargs: Keyword arguments to pass to the function
            
        Returns:
            Result of the function call
            
        Raises:
            Exception: The last exception if all retries fail
        """
        max_retries = 3
        retry_delay = 30  # 30 seconds as requested
        
        last_exception = None
        
        for attempt in range(max_retries + 1):  # 0, 1, 2, 3 (4 total attempts)
            try:
                result = func(*args, **kwargs)
                if attempt > 0:
                    logger.info(f"✓ Request succeeded after {attempt} retries")
                return result
                
            except Exception as e:
                last_exception = e
                error_str = str(e).lower()
                
                # Check for retryable server errors
                is_retryable = (
                    "500" in error_str or           # Internal Server Error
                    "503" in error_str or           # Service Unavailable  
                    "502" in error_str or           # Bad Gateway
                    "504" in error_str or           # Gateway Timeout
                    "internal" in error_str or      # Generic internal error
                    "server error" in error_str or  # Generic server error
                    "rate limit" in error_str or    # Rate limiting (temporary)
                    "quota" in error_str            # Quota exceeded (may be temporary)
                )
                
                if is_retryable and attempt < max_retries:
                    error_code = "500/503" if any(code in error_str for code in ["500", "503"]) else "SERVER"
                    logger.warning(f"{error_code} Server Error (attempt {attempt + 1}/{max_retries + 1}). Retrying in {retry_delay}s...")
                    logger.debug(f"Error details: {e}")
                    time.sleep(retry_delay)
                    continue
                else:
                    # Non-retryable error or max retries reached - stop immediately
                    if attempt >= max_retries:
                        logger.error(f"All {max_retries + 1} attempts failed. Last error: {e}")
                    break
        
        # All retries failed, raise the last exception
        raise last_exception
    
    @abstractmethod
    def _setup_model(self):
        """Setup model-specific initialization. Called during __init__."""
        pass
    
    @abstractmethod
    def _generate_tla_specification_impl(
        self, 
        source_code: str, 
        prompt_template: str,
        generation_config: Optional[GenerationConfig] = None
    ) -> GenerationResult:
        """
        Internal implementation of TLA+ specification generation.
        
        This method should be implemented by each adapter and contains
        the actual API call logic.
        
        Args:
            source_code: The source code to convert to TLA+
            prompt_template: Template for formatting the prompt
            generation_config: Generation parameters
            
        Returns:
            GenerationResult containing the generated TLA+ specification
            
        Raises:
            ModelError: If generation fails
        """
        pass
    
    def generate_tla_specification(
        self, 
        source_code: str, 
        prompt_template: str,
        generation_config: Optional[GenerationConfig] = None
    ) -> GenerationResult:
        """
        Generate TLA+ specification from source code with automatic retry on service unavailable.
        
        This method wraps the internal implementation with retry logic for handling
        503 Service Unavailable errors and similar temporary issues.
        
        Args:
            source_code: The source code to convert to TLA+
            prompt_template: Template for formatting the prompt
            generation_config: Generation parameters
            
        Returns:
            GenerationResult containing the generated TLA+ specification
            
        Raises:
            ModelError: If generation fails after all retries
        """
        return self._retry_on_service_unavailable(
            self._generate_tla_specification_impl,
            source_code,
            prompt_template,
            generation_config
        )
    
    def generate_direct(
        self, 
        complete_prompt: str,
        generation_config: Optional[GenerationConfig] = None
    ) -> GenerationResult:
        """
        Generate content using a complete, pre-formatted prompt.
        
        This method is for cases where the prompt has already been fully formatted
        (e.g., using Template.substitute()) and doesn't need further processing.
        
        Args:
            complete_prompt: Complete, ready-to-use prompt text
            generation_config: Generation parameters
            
        Returns:
            GenerationResult containing the generated content
            
        Raises:
            ModelError: If generation fails after all retries
        """
        return self._retry_on_service_unavailable(
            self._generate_direct_impl,
            complete_prompt,
            generation_config
        )
    
    @abstractmethod
    def _generate_direct_impl(
        self, 
        complete_prompt: str,
        generation_config: Optional[GenerationConfig] = None
    ) -> GenerationResult:
        """
        Internal implementation of direct generation from complete prompt.
        
        This method should be implemented by each adapter and contains
        the actual API call logic for pre-formatted prompts.
        
        Args:
            complete_prompt: Complete, ready-to-use prompt text
            generation_config: Generation parameters
            
        Returns:
            GenerationResult containing the generated content
        """
        pass
    
    @abstractmethod
    def is_available(self) -> bool:
        """
        Check if the model is available and properly configured.
        
        Returns:
            True if model can be used, False otherwise
        """
        pass
    
    def get_model_info(self) -> Dict[str, Any]:
        """
        Get information about the model.
        
        Returns:
            Dictionary containing model metadata
        """
        return {
            "model_name": self.model_name,
            "adapter_type": self.__class__.__name__,
            "config": self.config
        }

    def validate_config(self) -> List[str]:
        """
        Validate model configuration.
        
        Returns:
            List of validation error messages (empty if valid)
        """
        errors = []
        if not self.model_name:
            errors.append("model_name is required")
        return errors


class ModelError(Exception):
    """Custom exception for model-related errors."""
    pass


class ModelUnavailableError(ModelError):
    """Raised when a model is not available or not properly configured."""
    pass


class GenerationError(ModelError):
    """Raised when text generation fails."""
    pass


class RateLimitError(ModelError):
    """Raised when API rate limit is exceeded."""
    pass