"""
PAT Invariant Translator: Translates generic invariant templates to specific CSP assertions.

Uses LLM (Claude) to translate expert-written invariant templates into
concrete CSP# assertions for a given specification.
"""

import json
import logging
import time
from pathlib import Path
from string import Template
from typing import Dict, List, Tuple

from ...config import get_configured_model
from ...models.base import GenerationConfig
from .pat_invariant_loader import PATInvariantTemplate

logger = logging.getLogger(__name__)


class PATInvariantTranslator:
    """Translates generic PAT invariant templates to specific CSP assertions"""

    def __init__(self):
        """Initialize the translator"""
        self.name = "pat_invariant_translator"
        logger.info("PATInvariantTranslator initialized")

    def translate_all_invariants(
        self,
        templates: List[PATInvariantTemplate],
        csp_content: str,
        task_name: str,
        model_name: str
    ) -> Tuple[bool, Dict[str, str], str]:
        """
        Translate all invariant templates to specific CSP assertions.

        Note: Always uses Claude for translation as it produces the best results.
        The model_name parameter is kept for interface compatibility.

        Args:
            templates: List of invariant templates to translate
            csp_content: Target CSP specification content
            task_name: Name of the task (for loading prompt)
            model_name: Model name (kept for compatibility, Claude is always used)

        Returns:
            Tuple of (success, {invariant_name: csp_assertion}, error_message)
        """
        try:
            # Always use Claude for invariant translation
            claude_model_name = "claude"
            logger.info(
                f"Using Claude ({claude_model_name}) for PAT invariant translation "
                f"(original model: {model_name})"
            )
            model = get_configured_model(claude_model_name)

            # Load task-specific prompt template
            prompt_template = self._load_translation_prompt(task_name)

            # Format invariant templates for the prompt
            invariant_templates_text = self._format_templates_for_prompt(templates)

            # Format prompt
            template = Template(prompt_template)
            prompt = template.substitute(
                csp_specification=csp_content,
                invariant_templates=invariant_templates_text
            )

            logger.debug(f"Translation prompt length: {len(prompt)} chars")

            # Generate invariant implementations with JSON mode
            gen_config = GenerationConfig(
                use_json_mode=True  # Enable JSON mode for structured output
            )

            start_time = time.time()
            result = model.generate_direct(prompt, gen_config)
            end_time = time.time()

            logger.info(f"Translation took {end_time - start_time:.2f}s")

            if not result.success:
                error_msg = f"Translation failed: {result.error_message}"
                logger.error(error_msg)
                return False, {}, error_msg

            # Parse JSON response
            try:
                translations = json.loads(result.generated_text)
                logger.info(f"Successfully translated {len(translations)} invariants")

                # Validate that all templates were translated
                missing = []
                for template in templates:
                    if template.name not in translations:
                        missing.append(template.name)

                if missing:
                    logger.warning(f"Missing translations for: {missing}")

                return True, translations, ""

            except json.JSONDecodeError as e:
                error_msg = f"Failed to parse translation JSON: {e}\nResponse: {result.generated_text[:500]}"
                logger.error(error_msg)
                return False, {}, error_msg

        except Exception as e:
            error_msg = f"Translation exception: {str(e)}"
            logger.error(error_msg, exc_info=True)
            return False, {}, error_msg

    def _load_translation_prompt(self, task_name: str) -> str:
        """
        Load task-specific translation prompt template.

        Args:
            task_name: Name of the task

        Returns:
            Prompt template string
        """
        # Try to load task-specific prompt
        prompt_file = Path("data/prompts/pat_invariant_translation") / f"{task_name}.txt"

        if prompt_file.exists():
            logger.info(f"Loading task-specific translation prompt: {prompt_file}")
            with open(prompt_file, 'r', encoding='utf-8') as f:
                return f.read()

        # Fallback to generic prompt
        logger.info("Using generic PAT invariant translation prompt")
        return self._get_generic_translation_prompt()

    def _get_generic_translation_prompt(self) -> str:
        """
        Get generic translation prompt template.

        Returns:
            Generic prompt template
        """
        return """You are an expert in formal verification and PAT (Process Analysis Toolkit) CSP# specifications.

Your task is to translate generic invariant templates into concrete CSP# assertions for a specific specification.

# CSP# Specification
$csp_specification

# Invariant Templates
$invariant_templates

# Instructions
For each invariant template above, generate a concrete CSP# assertion that:
1. Uses the actual variable names, processes, and structures from the specification
2. Follows PAT CSP# syntax (use #define for formulas, #assert for assertions)
3. Preserves the semantic meaning of the invariant
4. Is syntactically correct and verifiable by PAT

# Output Format
Return a JSON object where keys are invariant names and values are complete CSP# assertion code:

{
  "InvariantName1": "#define formula1 = ...; #assert System |= [] formula1;",
  "InvariantName2": "#assert System deadlockfree;",
  ...
}

# Important Notes
- Use PAT CSP# syntax: #define, #assert, |=, [], <>, X (next), etc.
- For safety properties, use: #assert System |= [] property;
- For reachability, use: #assert System reaches goal;
- For deadlock freedom, use: #assert System deadlockfree;
- Ensure variable/process names match the specification exactly
- Each assertion should be self-contained and verifiable

Return ONLY the JSON object, no additional text."""

    def _format_templates_for_prompt(self, templates: List[PATInvariantTemplate]) -> str:
        """
        Format invariant templates for inclusion in the prompt.

        Args:
            templates: List of invariant templates

        Returns:
            Formatted string
        """
        lines = []

        for i, template in enumerate(templates, 1):
            lines.append(f"## Invariant {i}: {template.name}")
            lines.append(f"Type: {template.type}")
            lines.append(f"Natural Language: {template.natural_language}")
            lines.append(f"Formal Description: {template.formal_description}")
            lines.append(f"CSP# Example:")
            lines.append(template.csp_example)
            lines.append("")  # Blank line separator

        return "\n".join(lines)
