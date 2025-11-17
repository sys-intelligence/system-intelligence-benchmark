"""
ExistSpec Adapter: Mock adapter for using existing TLA+ specification files.

This adapter doesn't actually call any LLM but provides a consistent interface
for using existing TLA+ specifications in the benchmark framework.
"""

import time
from typing import Dict, Any, List, Optional

from .base import ModelAdapter, GenerationResult, GenerationConfig


class ExistSpecAdapter(ModelAdapter):
    """
    Mock adapter for using existing TLA+ specification files.
    
    This adapter doesn't generate new specifications but provides a consistent
    interface for evaluation workflows that use existing TLA+ files.
    """
    
    def __init__(self, **config):
        """Initialize the ExistSpec adapter."""
        super().__init__(
            model_name="with_exist_spec",
            provider="exist_spec",
            **config
        )
        
        # Override default config
        self.config.update({
            "max_tokens": 0,  # Not applicable
            "temperature": 0.0,  # Not applicable
            "description": "Use existing TLA+ specification files"
        })
    
    def validate_config(self) -> List[str]:
        """Validate adapter configuration."""
        # No external dependencies to validate
        return []
    
    def is_available(self) -> bool:
        """Check if adapter is available."""
        return True  # Always available
    
    def generate_tla_specification(
        self,
        source_code: str,
        prompt: str,
        config: Optional[GenerationConfig] = None
    ) -> GenerationResult:
        """
        Mock generation that returns empty result.
        
        This method is not meant to be called directly when using existing specs.
        The actual spec content should be provided via --spec-file parameter.
        """
        return GenerationResult(
            generated_text="",  # Empty - should use --spec-file instead
            metadata={
                "model": self.model_name,
                "provider": self.provider,
                "latency_seconds": 0.0,
                "note": "This adapter requires --spec-file parameter for actual content"
            },
            timestamp=time.time(),
            success=True,  # Success but with empty content
            error_message=None
        )
    
    def generate_direct(
        self,
        prompt: str,
        config: Optional[GenerationConfig] = None
    ) -> GenerationResult:
        """
        Mock direct generation that returns empty result.
        
        This method is not meant to be called directly when using existing specs.
        """
        return GenerationResult(
            generated_text="",  # Empty - should use --spec-file instead
            metadata={
                "model": self.model_name,
                "provider": self.provider,
                "latency_seconds": 0.0,
                "note": "This adapter requires existing files for actual content"
            },
            timestamp=time.time(),
            success=True,  # Success but with empty content
            error_message=None
        )
    
    def get_model_info(self) -> Dict[str, Any]:
        """Get information about the ExistSpec adapter."""
        return {
            "name": self.model_name,
            "provider": self.provider,
            "type": "mock_adapter",
            "description": "Use existing TLA+ specification files",
            "capabilities": [
                "existing_spec_support",
                "no_generation"
            ],
            "requirements": [
                "spec_file_parameter"
            ]
        }
    
    def __str__(self) -> str:
        return f"ExistSpecAdapter(model={self.model_name})"
    
    def __repr__(self) -> str:
        return self.__str__()