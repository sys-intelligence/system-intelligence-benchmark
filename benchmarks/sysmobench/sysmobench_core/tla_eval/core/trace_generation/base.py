"""
Base interface for system-specific trace generation and conversion.

This module defines the abstract interfaces that each system implementation
must provide for trace validation.
"""

from abc import ABC, abstractmethod
from typing import Dict, Any, List, Optional
from pathlib import Path


class TraceGenerator(ABC):
    """
    Abstract base class for system-specific trace generators.
    
    Each system (etcd, asterinas, etc.) should implement this interface
    to provide trace generation functionality.
    """
    
    @abstractmethod
    def generate_traces(self, config: Dict[str, Any], output_dir: Path, name_prefix: str = "trace") -> List[Dict[str, Any]]:
        """
        Generate runtime traces for the system.
        
        Args:
            config: System-specific configuration parameters (including 'num_traces' if relevant)
            output_dir: Directory where trace files should be saved
            name_prefix: Prefix for trace file names
            
        Returns:
            List of dictionaries with generation results for each trace:
            [
                {
                    "success": bool,
                    "trace_file": str,  # Path to generated trace file
                    "event_count": int,
                    "duration": float,
                    "metadata": Dict[str, Any]  # System-specific metadata
                },
                ...
            ]
        """
        pass
    
    def generate_trace(self, config: Dict[str, Any], output_path: Path) -> Dict[str, Any]:
        """
        Generate a single runtime trace (backward compatibility).
        
        Default implementation calls generate_traces() and returns first result.
        """
        results = self.generate_traces(config, output_path.parent, output_path.stem)
        return results[0] if results else {"success": False, "error": "No traces generated"}
    
    @abstractmethod
    def get_default_config(self) -> Dict[str, Any]:
        """
        Get default configuration for this system's trace generation.
        
        Returns:
            Dictionary with default configuration parameters
        """
        pass
    
    @abstractmethod
    def get_available_scenarios(self) -> Dict[str, Dict[str, Any]]:
        """
        Get available predefined scenarios for this system.
        
        Returns:
            Dictionary mapping scenario names to their configurations
        """
        pass


class TraceConverter(ABC):
    """
    Abstract base class for system-specific trace converters.
    
    Each system should implement this interface to convert raw system traces
    to TLA+ specification-compatible format.
    """
    
    @abstractmethod
    def convert_trace(self, input_path: Path, output_path: Path) -> Dict[str, Any]:
        """
        Convert system trace to TLA+ specification-compatible format.
        
        Args:
            input_path: Path to the raw system trace file
            output_path: Path where converted trace should be saved
            
        Returns:
            Dictionary with conversion results:
            {
                "success": bool,
                "input_events": int,
                "output_transitions": int,
                "output_file": str,  # Path to converted trace file
                "error": str  # Error message if success=False
            }
        """
        pass


class SystemModule(ABC):
    """
    Abstract base class for complete system implementations.
    
    Each system directory should provide a module implementing this interface,
    containing both trace generation and conversion functionality.
    """
    
    @abstractmethod
    def get_trace_generator(self) -> TraceGenerator:
        """Get the trace generator for this system."""
        pass
    
    @abstractmethod
    def get_trace_converter(self) -> TraceConverter:
        """Get the trace converter for this system."""
        pass
    
    @abstractmethod
    def get_system_name(self) -> str:
        """Get the name identifier for this system."""
        pass