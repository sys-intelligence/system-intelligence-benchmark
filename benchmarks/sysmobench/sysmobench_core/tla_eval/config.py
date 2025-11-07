"""
Configuration management for model settings.

This module handles loading and managing model configurations,
allowing users to define their models in config files.
"""

import yaml
import os
import logging
from pathlib import Path
from typing import Dict, Any
from .models import get_model_adapter

logger = logging.getLogger(__name__)


class ConfigManager:
    """Manages model configurations from YAML files."""
    
    def __init__(self, config_path: str = "config/models.yaml"):
        """
        Initialize configuration manager.
        
        Args:
            config_path: Path to model configuration file
        """
        self.config_path = config_path
        self.config = self._load_config()
        
    def _load_config(self) -> Dict[str, Any]:
        """Load configuration from YAML file."""
        config_file = Path(self.config_path)
        
        if not config_file.exists():
            raise FileNotFoundError(f"Config file not found: {self.config_path}")
            
        with open(config_file, 'r', encoding='utf-8') as f:
            config = yaml.safe_load(f)
            
        if not config or 'models' not in config:
            raise ValueError(f"Invalid config file: missing 'models' section")
            
        return config
    
    def get_model(self, model_name: str = None):
        """
        Get a configured model adapter.
        
        Args:
            model_name: Name of model in config, or None for default
            
        Returns:
            ModelAdapter instance
        """
        if model_name is None:
            model_name = self.config.get('default_model')
            if not model_name:
                raise ValueError("No model specified and no default_model in config")
        
        if model_name not in self.config['models']:
            available = list(self.config['models'].keys())
            raise ValueError(f"Model '{model_name}' not found. Available: {available}")
        
        model_config = self.config['models'][model_name].copy()
        provider = model_config.pop('provider')
        model_id = model_config.pop('model_name')
        
        # Handle API key from environment
        if 'api_key_env' in model_config:
            env_var = model_config.pop('api_key_env')
            api_key = os.getenv(env_var)
            if api_key:
                model_config['api_key'] = api_key
            else:
                logger.warning(f"Environment variable {env_var} not set for model {model_name}")
        
        return get_model_adapter(provider, model_name=model_id, **model_config)
    
    def list_available_models(self) -> list:
        """List all configured model names."""
        return list(self.config['models'].keys())
    
    def get_default_model_name(self) -> str:
        """Get the default model name."""
        return self.config.get('default_model', list(self.config['models'].keys())[0])


# Global config manager instance
_config_manager = None

def get_config_manager(config_path: str = "config/models.yaml") -> ConfigManager:
    """Get global configuration manager instance."""
    global _config_manager
    if _config_manager is None:
        _config_manager = ConfigManager(config_path)
    return _config_manager

def get_configured_model(model_name: str = None):
    """Convenience function to get a configured model."""
    return get_config_manager().get_model(model_name)