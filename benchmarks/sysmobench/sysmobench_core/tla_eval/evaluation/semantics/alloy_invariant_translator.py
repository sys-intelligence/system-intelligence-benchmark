"""
Alloy Invariant Translator: Translates generic invariant templates to specific Alloy specifications.

This module mirrors the TLA+ InvariantTranslator design but adapted for Alloy syntax.
"""

import json
import logging
import time
from pathlib import Path
from string import Template
from typing import Dict, List, Tuple
from dataclasses import dataclass

from ...config import get_configured_model
from ...models.base import GenerationConfig

logger = logging.getLogger(__name__)


@dataclass
class AlloyInvariantTemplate:
    """Represents a single Alloy invariant template from the YAML file"""
    name: str
    type: str  # "safety" or "liveness"
    natural_language: str
    formal_description: str
    alloy_example: str


class AlloyInvariantTemplateLoader:
    """Loads Alloy invariant templates from YAML files"""

    def __init__(self, templates_dir: str = "data/alloy_invariant_templates"):
        self.templates_dir = Path(templates_dir)

    def load_task_invariants(self, task_name: str) -> List[AlloyInvariantTemplate]:
        """
        Load invariant templates for a specific task.

        Args:
            task_name: Name of the task (e.g., "spin")

        Returns:
            List of AlloyInvariantTemplate objects
        """
        import yaml

        invariants_file = self.templates_dir / task_name / "invariants.yaml"

        if not invariants_file.exists():
            raise FileNotFoundError(f"Invariants file not found: {invariants_file}")

        with open(invariants_file, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)

        templates = []
        for inv_data in data.get('invariants', []):
            template = AlloyInvariantTemplate(
                name=inv_data['name'],
                type=inv_data['type'],
                natural_language=inv_data['natural_language'],
                formal_description=inv_data['formal_description'],
                alloy_example=inv_data['alloy_example']
            )
            templates.append(template)

        logger.info(f"Loaded {len(templates)} Alloy invariant templates for task: {task_name}")
        return templates


class AlloyInvariantTranslator:
    """Translates generic Alloy invariant templates to specific Alloy specifications"""

    def __init__(self):
        self.name = "alloy_invariant_translator"

    def translate_all_invariants(self,
                                templates: List[AlloyInvariantTemplate],
                                alloy_content: str,
                                task_name: str,
                                model_name: str) -> Tuple[bool, Dict[str, str], str]:
        """
        Translate all invariant templates to the specific Alloy specification in one call.

        Note: Always uses GPT-5 for translation as it produces the best results.
        The model_name parameter is kept for interface compatibility but GPT-5 is used internally.

        Args:
            templates: List of invariant templates to translate
            alloy_content: Target Alloy specification content
            task_name: Name of the task (for loading prompt)
            model_name: Model name (ignored, Claude is always used for translation)

        Returns:
            Tuple of (success, {invariant_name: translated_invariant}, error_message)
        """
        try:
            # Always use GPT-5 for invariant translation as it produces the best results
            gpt5_model_name = "gpt5"
            logger.info(f"Using GPT-5 ({gpt5_model_name}) for invariant translation (original model: {model_name})")
            model = get_configured_model(gpt5_model_name)

            # Load task-specific prompt template
            prompt_template = self._load_translation_prompt(task_name)

            # Format invariant templates for the prompt
            invariant_templates_text = self._format_templates_for_prompt(templates)

            # Format prompt with Alloy specification and templates
            template = Template(prompt_template)
            prompt = template.substitute(
                alloy_specification=alloy_content,
                invariant_templates=invariant_templates_text
            )

            # Generate invariant implementations with JSON mode
            gen_config = GenerationConfig(
                use_json_mode=True  # Enable JSON mode for structured output
            )

            start_time = time.time()
            result = model.generate_direct(prompt, gen_config)
            end_time = time.time()

            if not result.success:
                return False, {}, result.error_message

            logger.info(f"Generated text length: {len(result.generated_text)} characters")

            # DEBUG: Log the generated text content for debugging
            logger.debug("=== GENERATED TEXT START ===")
            logger.debug(result.generated_text)
            logger.debug("=== GENERATED TEXT END ===")

            # Parse the generated invariants
            translated_invariants = self._parse_generated_invariants(
                result.generated_text, templates
            )

            logger.info(f"Successfully translated {len(translated_invariants)} invariants in {end_time - start_time:.2f}s")
            return True, translated_invariants, None

        except Exception as e:
            logger.error(f"Alloy invariant translation failed: {e}")
            return False, {}, str(e)

    def _load_translation_prompt(self, task_name: str) -> str:
        """Load task-specific prompt for Alloy invariant translation"""
        from ...tasks.loader import get_task_loader
        task_loader = get_task_loader()

        # Get task directory path
        tasks_dir = task_loader.tasks_dir
        prompt_file = tasks_dir / task_name / "prompts" / "alloy" / "phase3_invariant_implementation.txt"

        if not prompt_file.exists():
            raise FileNotFoundError(f"Phase 3 Alloy invariant prompt not found: {prompt_file}")

        with open(prompt_file, 'r', encoding='utf-8') as f:
            return f.read()

    def _format_templates_for_prompt(self, templates: List[AlloyInvariantTemplate]) -> str:
        """Format invariant templates for inclusion in the prompt"""
        formatted_templates = []

        for template in templates:
            formatted = f"""
### {template.name} ({template.type.upper()})
**Description**: {template.natural_language}

**Formal**: {template.formal_description}

**Alloy Example**:
```
{template.alloy_example.strip()}
```
"""
            formatted_templates.append(formatted)

        return '\n'.join(formatted_templates)

    def _parse_generated_invariants(self,
                                  generated_text: str,
                                  templates: List[AlloyInvariantTemplate]) -> Dict[str, str]:
        """Parse the generated text to extract individual Alloy invariant definitions"""
        translated_invariants = {}

        try:
            # Clean the text: remove markdown code blocks if present
            clean_text = generated_text.strip()
            if clean_text.startswith('```json'):
                # Remove ```json from start and ``` from end
                lines = clean_text.split('\n')
                if lines[0].strip() == '```json' and lines[-1].strip() == '```':
                    clean_text = '\n'.join(lines[1:-1])
            elif clean_text.startswith('```'):
                # Remove generic ``` blocks
                lines = clean_text.split('\n')
                if lines[0].strip() == '```' and lines[-1].strip() == '```':
                    clean_text = '\n'.join(lines[1:-1])

            data = json.loads(clean_text)

            # Expect format: {"invariants": ["assert Name { ... }\ncheck Name ...", ...]}
            if isinstance(data, dict) and "invariants" in data:
                invariant_list = data["invariants"]
                if isinstance(invariant_list, list):
                    logger.info("Parsing JSON format Alloy invariants")

                    for i, invariant_definition in enumerate(invariant_list):
                        logger.debug(f"Processing invariant {i+1}: {len(invariant_definition)} chars")

                        if isinstance(invariant_definition, str) and invariant_definition.strip():
                            # Extract invariant name from the definition (after "assert" and before "{")
                            # Format: "assert InvariantName { ... }\ncheck InvariantName ..."
                            invariant_name = None
                            if 'assert' in invariant_definition:
                                # Find the name between "assert" and "{"
                                assert_idx = invariant_definition.find('assert')
                                brace_idx = invariant_definition.find('{', assert_idx)
                                if assert_idx != -1 and brace_idx != -1:
                                    name_part = invariant_definition[assert_idx + 6:brace_idx].strip()
                                    invariant_name = name_part

                            if invariant_name:
                                # Find matching template by name
                                for template in templates:
                                    if template.name.lower() == invariant_name.lower():
                                        translated_invariants[template.name] = invariant_definition
                                        logger.info(f"✓ Stored invariant: {template.name}")
                                        break
                                else:
                                    logger.warning(f"No matching template for: {invariant_name}")
                            else:
                                logger.warning(f"Could not extract invariant name from: {invariant_definition[:100]}...")
                        else:
                            logger.warning(f"Skipped empty or invalid invariant: {repr(invariant_definition[:50] if invariant_definition else '')}")

                    return translated_invariants

            logger.error(f"Unexpected JSON structure: {data}")
            return {}

        except json.JSONDecodeError as e:
            logger.error(f"JSON parsing failed: {e}")
            logger.error(f"Attempted to parse: {clean_text[:500]}...")
            return {}
        except Exception as e:
            logger.error(f"Unexpected error during parsing: {e}")
            return {}


# Convenience function
def create_alloy_invariant_translator() -> AlloyInvariantTranslator:
    """Factory function to create an Alloy invariant translator."""
    return AlloyInvariantTranslator()
