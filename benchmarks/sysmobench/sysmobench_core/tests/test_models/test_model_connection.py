#!/usr/bin/env python3
"""
Test model connections and basic functionality.

This test verifies that configured models can connect properly
and respond to basic requests.
"""

import os
import sys
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent.parent
sys.path.insert(0, str(project_root))

from tla_eval.config import get_config_manager, get_configured_model
from tla_eval.models.base import GenerationConfig


def test_model_connection(model_name: str):
    """
    Test connection to a specific model.
    
    Args:
        model_name: Name of model in config to test
    """
    print(f"\n{'='*50}")
    print(f"Testing model: {model_name}")
    print(f"{'='*50}")
    
    try:
        # Get configured model
        model = get_configured_model(model_name)
        print(f"✓ Model initialized successfully")
        print(f"  Model info: {model.get_model_info()}")
        
        # Check if model is available
        if not model.is_available():
            print(f"✗ Model is not available (check API keys)")
            return False
        
        print(f"✓ Model is available")
        
        # Test basic generation with greeting
        test_prompt = "Hello! Please respond with a simple greeting and tell me you're working correctly."
        
        print(f"Sending test message...")
        print(f"Prompt: {test_prompt}")
        
        # Generate response
        generation_config = GenerationConfig(max_tokens=100, temperature=0.1)
        result = model.generate_tla_specification("", test_prompt, generation_config)
        
        if result.success:
            print(f"✓ Generation successful!")
            print(f"\nModel Response:")
            print(f"{'─'*40}")
            print(result.generated_text)
            print(f"{'─'*40}")
            
            print(f"\nGeneration Metadata:")
            for key, value in result.metadata.items():
                print(f"  {key}: {value}")
            
            return True
        else:
            print(f"✗ Generation failed: {result.error_message}")
            return False
            
    except Exception as e:
        print(f"✗ Error testing model {model_name}: {e}")
        return False


def test_all_configured_models():
    """Test all models in the configuration."""
    print("Testing all configured models...")
    
    try:
        config_manager = get_config_manager()
        available_models = config_manager.list_available_models()
        
        print(f"Found {len(available_models)} configured models: {available_models}")
        
        success_count = 0
        total_count = len(available_models)
        
        for model_name in available_models:
            if test_model_connection(model_name):
                success_count += 1
        
        print(f"\n{'='*60}")
        print(f"Test Summary: {success_count}/{total_count} models working")
        print(f"{'='*60}")
        
        if success_count == 0:
            print("⚠️  No models are working. Check your API keys and configuration.")
        elif success_count < total_count:
            print("⚠️  Some models failed. Check failed models' API keys.")
        else:
            print("🎉 All models are working correctly!")
            
        return success_count > 0
        
    except Exception as e:
        print(f"Error loading configuration: {e}")
        return False


def test_specific_model():
    """Test a specific model chosen by user."""
    try:
        config_manager = get_config_manager()
        available_models = config_manager.list_available_models()
        
        print("Available models:")
        for i, model_name in enumerate(available_models, 1):
            print(f"  {i}. {model_name}")
        
        choice = input(f"\nEnter model number to test (1-{len(available_models)}), or 'all' for all models: ").strip()
        
        if choice.lower() == 'all':
            return test_all_configured_models()
        
        try:
            model_index = int(choice) - 1
            if 0 <= model_index < len(available_models):
                model_name = available_models[model_index]
                return test_model_connection(model_name)
            else:
                print("Invalid choice")
                return False
        except ValueError:
            print("Invalid input")
            return False
            
    except Exception as e:
        print(f"Error: {e}")
        return False


def main():
    """Main test function."""
    print("🧪 Model Connection Test")
    print("This test verifies that your configured models can connect and respond properly.")
    
    # Check if config file exists
    config_path = "config/models.yaml"
    if not Path(config_path).exists():
        print(f"❌ Configuration file not found: {config_path}")
        print("Please create a model configuration file first.")
        return
    
    # Show API key status
    print(f"\n📋 API Key Status:")
    api_keys = {
        "OPENAI_API_KEY": os.getenv("OPENAI_API_KEY", "Not set"),
        "ANTHROPIC_API_KEY": os.getenv("ANTHROPIC_API_KEY", "Not set"),
        "YUNWU_API_KEY": os.getenv("YUNWU_API_KEY", "Not set"),
    }
    
    for key, value in api_keys.items():
        status = "✓ Set" if value != "Not set" else "❌ Not set"
        print(f"  {key}: {status}")
    
    print(f"\n" + "="*60)
    
    # Run tests
    try:
        success = test_all_configured_models()
        
        if not success:
            print(f"\n💡 Troubleshooting tips:")
            print(f"   1. Check that your API keys are set correctly")
            print(f"   2. Verify your model names in config/models.yaml")
            print(f"   3. Check your internet connection")
            print(f"   4. For custom APIs, verify the URL is correct")
            
    except KeyboardInterrupt:
        print(f"\n\nTest interrupted by user.")
    except Exception as e:
        print(f"Unexpected error: {e}")


if __name__ == "__main__":
    main()