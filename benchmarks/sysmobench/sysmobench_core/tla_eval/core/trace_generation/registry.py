"""
System registry for dynamic loading of trace generation systems.

This module provides a centralized way to register and load system-specific
trace generation implementations.
"""

import importlib
import os
from pathlib import Path
from typing import Dict, Optional
from .base import SystemModule


class SystemRegistry:
    """
    Registry for managing system-specific trace generation modules.
    
    This class handles dynamic discovery and loading of system implementations
    from the tla_eval/core/trace_generation/{system}/ directories.
    """
    
    def __init__(self):
        self._systems: Dict[str, SystemModule] = {}
        self._discover_systems()
    
    def _discover_systems(self):
        """
        Automatically discover available systems by scanning subdirectories.
        
        Each system directory should contain a module.py file that implements
        the SystemModule interface.
        """
        current_dir = Path(__file__).parent
        
        # Scan for system directories
        for item in current_dir.iterdir():
            if item.is_dir() and not item.name.startswith('_') and item.name != '__pycache__':
                system_name = item.name
                module_file = item / 'module.py'
                
                if module_file.exists():
                    try:
                        # Import the system module
                        module_path = f"tla_eval.core.trace_generation.{system_name}.module"
                        module = importlib.import_module(module_path)
                        
                        # Get the system implementation
                        if hasattr(module, 'get_system'):
                            system_impl = module.get_system()
                            if isinstance(system_impl, SystemModule):
                                self._systems[system_name] = system_impl
                                print(f"Registered trace generation system: {system_name}")
                            else:
                                print(f"Warning: {system_name} module.get_system() doesn't return SystemModule")
                        else:
                            print(f"Warning: {system_name} module.py missing get_system() function")
                            
                    except Exception as e:
                        print(f"Warning: Failed to load system '{system_name}': {e}")
    
    def get_system(self, system_name: str) -> Optional[SystemModule]:
        """
        Get a system implementation by name.
        
        Args:
            system_name: Name of the system (e.g., "etcd", "asterinas")
            
        Returns:
            SystemModule implementation or None if not found
        """
        return self._systems.get(system_name)
    
    def get_available_systems(self) -> Dict[str, SystemModule]:
        """
        Get all available system implementations.
        
        Returns:
            Dictionary mapping system names to their implementations
        """
        return self._systems.copy()
    
    def is_system_supported(self, system_name: str) -> bool:
        """
        Check if a system is supported.
        
        Args:
            system_name: Name of the system to check
            
        Returns:
            True if system is supported, False otherwise
        """
        return system_name in self._systems


# Global registry instance
_registry = SystemRegistry()


def get_system(system_name: str) -> Optional[SystemModule]:
    """
    Get a system implementation by name.
    
    Args:
        system_name: Name of the system (e.g., "etcd", "asterinas")
        
    Returns:
        SystemModule implementation or None if not found
    """
    return _registry.get_system(system_name)


def get_available_systems() -> Dict[str, SystemModule]:
    """
    Get all available system implementations.
    
    Returns:
        Dictionary mapping system names to their implementations
    """
    return _registry.get_available_systems()


def is_system_supported(system_name: str) -> bool:
    """
    Check if a system is supported.
    
    Args:
        system_name: Name of the system to check
        
    Returns:
        True if system is supported, False otherwise
    """
    return _registry.is_system_supported(system_name)