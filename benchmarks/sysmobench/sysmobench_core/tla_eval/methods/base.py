"""
Base class for TLA+ generation methods.

This module defines the interface that all TLA+ generation methods must implement.
"""

from abc import ABC, abstractmethod
from typing import Dict, Any, List, Tuple
from dataclasses import dataclass


@dataclass
class GenerationTask:
    """A TLA+ generation task with source code and metadata."""
    source_code: str
    task_name: str
    system_type: str  # e.g., "distributed", "concurrent"
    language: str     # e.g., "go", "java", "c++"
    description: str
    traces: List[List[Tuple[str, str]] | Tuple[str, str]] = None
    spec_module: str = None  # TLA+ module name for the specification
    extra_info: Dict[str, Any] = None  # Additional task-specific information
    
    def __post_init__(self):
        if self.extra_info is None:
            self.extra_info = {}


@dataclass  
class GenerationOutput:
    """Output from TLA+ generation method."""
    tla_specification: str
    method_name: str
    task_name: str
    metadata: Dict[str, Any]  # Method-specific metadata
    success: bool = True
    error_message: str = None


class TLAGenerationMethod(ABC):
    """
    Abstract base class for TLA+ generation methods.
    
    All generation methods (direct_call, agent_based, etc.) must inherit from this class.
    """
    
    def __init__(self, name: str):
        """
        Initialize the generation method.
        
        Args:
            name: Name of this method
        """
        self.name = name
    
    @abstractmethod
    def generate(self, task: GenerationTask, model_name: str = None) -> GenerationOutput:
        """
        Generate TLA+ specification from source code.
        
        Args:
            task: Generation task with source code and metadata
            model_name: Name of model to use (from config), or None for default
            
        Returns:
            GenerationOutput with TLA+ specification and metadata
        """
        pass
    
    @abstractmethod
    def get_method_info(self) -> Dict[str, Any]:
        """
        Get information about this generation method.
        
        Returns:
            Dictionary with method metadata
        """
        pass