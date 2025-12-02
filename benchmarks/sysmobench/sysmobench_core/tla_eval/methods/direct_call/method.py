"""
Direct call method implementation.

This method generates TLA+ specifications by directly prompting an LLM
with source code and asking for a TLA+ translation.
"""

from typing import Dict, Any
from ..base import TLAGenerationMethod, GenerationTask, GenerationOutput, format_prompt_template
from ...config import get_configured_model


class DirectCallMethod(TLAGenerationMethod):
    """
    Direct call method for TLA+ generation.
    
    This method uses a simple prompt to ask the LLM to convert
    source code directly to TLA+ specification.
    """
    
    def __init__(self):
        super().__init__("direct_call")
        
    def generate(self, task: GenerationTask, model_name: str = None) -> GenerationOutput:
        """
        Generate TLA+ specification using direct LLM call.
        
        Args:
            task: Generation task with source code
            model_name: Model to use from config
            
        Returns:
            GenerationOutput with TLA+ specification
        """
        try:
            # Get configured model
            model = get_configured_model(model_name)

            # Create prompt
            prompt = self._create_prompt(task)

            # Create generation config from model's YAML configuration
            from ...models.base import GenerationConfig
            generation_config = GenerationConfig(
                max_tokens=model.config.get('max_tokens'),
                temperature=model.config.get('temperature'),
                top_p=model.config.get('top_p')  # Only if defined in YAML
            )
            
            # Generate TLA+ specification
            result = model.generate_tla_specification(task.source_code, prompt, generation_config)
            
            # Return output
            return GenerationOutput(
                tla_specification=result.generated_text,
                method_name=self.name,
                task_name=task.task_name,
                metadata={
                    "model_info": model.get_model_info(),
                    "generation_metadata": result.metadata,
                    "prompt_template": "direct_call_basic"
                },
                success=result.success,
                error_message=result.error_message
            )
            
        except Exception as e:
            return GenerationOutput(
                tla_specification="",
                method_name=self.name,
                task_name=task.task_name,
                metadata={},
                success=False,
                error_message=str(e)
            )
    
    def _create_prompt(self, task: GenerationTask) -> str:
        """Create prompt for direct call method using task-specific prompt."""
        
        # Get task-specific prompt template (lazy import to avoid circular dependency)
        from ...tasks.loader import get_task_loader
        task_loader = get_task_loader()
        prompt_template = task_loader.get_task_prompt(
            task.task_name,
            self.name,
            task.spec_language
        )
        
        # Prepare format variables
        format_vars = {
            'language': task.language,
            'description': task.description,
            'system_type': task.system_type,
            'source_code': '{source_code}'  # Keep this placeholder for the model adapter
        }
        
        # Add extra info if available
        if task.extra_info:
            format_vars.update(task.extra_info)
        
        # Format template with task information without interfering with literal braces
        return format_prompt_template(prompt_template, format_vars)
    
    def get_method_info(self) -> Dict[str, Any]:
        """Get information about direct call method."""
        return {
            "name": self.name,
            "description": "Direct LLM call with basic prompt",
            "type": "single_shot",
            "requires_model": True,
            "supports_iteration": False
        }
