"""
Manual Invariant Evaluator: Phase 3 evaluation for TLA+ specifications.

This evaluator implements the third phase of evaluation which includes:
1. Loading expert-written invariant templates for the task
2. Using LLM to translate generic invariants to the specific TLA+ specification  
3. Running TLC model checking with the translated invariants
4. Reporting detailed results for each invariant test
"""

import os
import logging
import time
import yaml
from pathlib import Path
from string import Template
from typing import Dict, Any, List, Optional, Tuple
from dataclasses import dataclass

from ...models.base import GenerationResult, GenerationConfig
from ...config import get_configured_model
from ...utils.output_manager import get_output_manager
from ..base.evaluator import BaseEvaluator
from ..base.result_types import SemanticEvaluationResult

# Import TLC runner from runtime_check
from .runtime_check import TLCRunner, ConfigGenerator

logger = logging.getLogger(__name__)


@dataclass
class InvariantTemplate:
    """Represents a single invariant template from the YAML file"""
    name: str
    type: str  # "safety" or "liveness" 
    natural_language: str
    formal_description: str
    tla_example: str


@dataclass  
class InvariantTestResult:
    """Result of testing a single invariant"""
    name: str
    success: bool
    translated_invariant: str
    error_message: Optional[str] = None
    states_explored: int = 0
    verification_time: float = 0.0
    tlc_output: str = ""


class InvariantTemplateLoader:
    """Loads invariant templates from YAML files"""
    
    def __init__(self, templates_dir: str = "data/invariant_templates"):
        self.templates_dir = Path(templates_dir)
    
    def load_task_invariants(self, task_name: str) -> List[InvariantTemplate]:
        """
        Load invariant templates for a specific task.
        
        Args:
            task_name: Name of the task (e.g., "etcd", "spin")
            
        Returns:
            List of InvariantTemplate objects
        """
        invariants_file = self.templates_dir / task_name / "invariants.yaml"
        
        if not invariants_file.exists():
            raise FileNotFoundError(f"Invariants file not found: {invariants_file}")
        
        with open(invariants_file, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)
        
        templates = []
        for inv_data in data.get('invariants', []):
            template = InvariantTemplate(
                name=inv_data['name'],
                type=inv_data['type'],
                natural_language=inv_data['natural_language'],
                formal_description=inv_data['formal_description'],
                tla_example=inv_data['tla_example']
            )
            templates.append(template)
        
        logger.info(f"Loaded {len(templates)} invariant templates for task: {task_name}")
        return templates


class InvariantTranslator:
    """Translates generic invariant templates to specific TLA+ specifications"""
    
    def __init__(self):
        self.name = "invariant_translator"
    
    def translate_all_invariants(self, 
                                templates: List[InvariantTemplate],
                                tla_content: str, 
                                task_name: str, 
                                model_name: str) -> Tuple[bool, Dict[str, str], str]:
        """
        Translate all invariant templates to the specific TLA+ specification in one call.
        
        Note: Always uses Claude for translation as it produces the best results.
        The model_name parameter is kept for interface compatibility but Claude is used internally.
        
        Args:
            templates: List of invariant templates to translate
            tla_content: Target TLA+ specification content
            task_name: Name of the task (for loading prompt)
            model_name: Model name (ignored, Claude is always used for translation)
            
        Returns:
            Tuple of (success, {invariant_name: translated_invariant}, error_message)
        """
        try:
            # Always use Claude for invariant translation as it produces the best results
            # This is a "usage" of LLM rather than "evaluation", so we want consistency
            claude_model_name = "claude"  # Use available Claude model
            logger.info(f"Using Claude ({claude_model_name}) for invariant translation (original model: {model_name})")
            model = get_configured_model(claude_model_name)
            
            # Load task-specific prompt template
            prompt_template = self._load_translation_prompt(task_name)
            
            # Format invariant templates for the prompt
            invariant_templates_text = self._format_templates_for_prompt(templates)
            
            # Format prompt with TLA+ specification and templates
            template = Template(prompt_template)
            prompt = template.substitute(
                tla_specification=tla_content,
                invariant_templates=invariant_templates_text
            )
            
            # Generate invariant implementations - use model's configured values
            # Don't override the model's configuration, let it use configured temperature and max_tokens
            gen_config = GenerationConfig(
                use_json_mode=True  # Enable JSON mode for structured output
                # Note: temperature and max_tokens not set - will use model's configured values
            )
            
            start_time = time.time()
            result = model.generate_direct(prompt, gen_config)
            end_time = time.time()
            
            if not result.success:
                return False, {}, result.error_message

            logger.info(f"Generated text length: {len(result.generated_text)} characters")

            # DEBUG: Log the generated text content for debugging
            logger.info("=== GENERATED TEXT START ===")
            logger.info(result.generated_text)
            logger.info("=== GENERATED TEXT END ===")

            # Parse the generated invariants
            translated_invariants = self._parse_generated_invariants(
                result.generated_text, templates
            )
            
            logger.info(f"Successfully translated {len(translated_invariants)} invariants in {end_time - start_time:.2f}s")
            return True, translated_invariants, None
            
        except Exception as e:
            logger.error(f"Invariant translation failed: {e}")
            return False, {}, str(e)
    
    def _load_translation_prompt(self, task_name: str) -> str:
        """Load task-specific prompt for invariant translation"""
        from ...tasks.loader import get_task_loader
        task_loader = get_task_loader()
        
        # Get task directory path
        tasks_dir = task_loader.tasks_dir
        prompt_file = tasks_dir / task_name / "prompts" / "phase3_invariant_implementation.txt"
        
        if not prompt_file.exists():
            raise FileNotFoundError(f"Phase 3 invariant prompt not found: {prompt_file}")
        
        with open(prompt_file, 'r', encoding='utf-8') as f:
            return f.read()
    
    def _format_templates_for_prompt(self, templates: List[InvariantTemplate]) -> str:
        """Format invariant templates for inclusion in the prompt"""
        formatted_templates = []
        
        for template in templates:
            formatted = f"""
### {template.name} ({template.type.upper()})
**Description**: {template.natural_language}

**Formal**: {template.formal_description}

**TLA+ Example**:
```
{template.tla_example.strip()}
```
"""
            formatted_templates.append(formatted)
        
        return '\n'.join(formatted_templates)
    
    def _parse_generated_invariants(self, 
                                  generated_text: str, 
                                  templates: List[InvariantTemplate]) -> Dict[str, str]:
        """Parse the generated text to extract individual invariant definitions"""
        translated_invariants = {}
        
        try:
            # Try to parse as JSON first
            import json
            
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
            
            # Expect format: {"invariants": ["Name == Expression", ...]}
            if isinstance(data, dict) and "invariants" in data:
                invariant_list = data["invariants"]
                if isinstance(invariant_list, list):
                    logger.info("Parsing JSON format invariants")
                    
                    for i, invariant_definition in enumerate(invariant_list):
                        logger.info(f"Processing invariant {i+1}: {len(invariant_definition)} chars")
                        
                        if isinstance(invariant_definition, str) and invariant_definition.strip():
                            # Extract invariant name from the definition (everything before '==')
                            invariant_name = invariant_definition.split('==')[0].strip()
                            
                            # Find matching template by name
                            for template in templates:
                                if template.name.lower() == invariant_name.lower():
                                    translated_invariants[template.name] = invariant_definition
                                    logger.info(f"✓ Stored invariant: {template.name}")
                                    break
                            else:
                                logger.warning(f"No matching template for: {invariant_name}")
                        else:
                            logger.warning(f"Skipped empty or invalid invariant: {repr(invariant_definition[:50])}")
                    
                    return translated_invariants
            
        except json.JSONDecodeError as e:
            logger.info(f"JSON parsing failed: {e}, falling back to line-based parsing")
            logger.info(f"Attempted to parse: {clean_text[:500]}...")
        
        # Fallback to original line-based parsing for backward compatibility
        lines = generated_text.strip().split('\n')
        logger.info(f"Attempting line-based parsing with {len(lines)} lines")

        for i, line in enumerate(lines):
            line = line.strip()
            if not line or line.startswith('```') or line.startswith('#'):
                continue
            
            # Look for pattern: InvariantName == <expression>
            if ' == ' in line:
                logger.info(f"Found potential invariant line {i+1}: {line}")
                parts = line.split(' == ', 1)
                if len(parts) == 2:
                    invariant_name = parts[0].strip()
                    invariant_definition = line  # Keep the full definition
                    logger.info(f"Extracted invariant name: '{invariant_name}'")

                    # Match to template names (case-insensitive)
                    for template in templates:
                        if template.name.lower() == invariant_name.lower():
                            translated_invariants[template.name] = invariant_definition
                            logger.info(f"✓ Matched and stored invariant: {template.name}")
                            break
                    else:
                        logger.info(f"No matching template found for: '{invariant_name}'")
            else:
                logger.debug(f"Line {i+1} doesn't contain ' == ': {line[:50]}...")
        
        return translated_invariants


class StaticConfigGenerator:
    """
    Static configuration generator that creates .cfg files by string manipulation
    instead of LLM generation. Generates a base .cfg once, then adds invariants statically.
    """
    
    def __init__(self):
        self.base_config_cache = {}  # Cache base configs by task_name
        self.llm_config_generator = ConfigGenerator()  # Fallback to LLM generation
    
    def generate_config_for_invariant(self, 
                                    tla_content: str,
                                    invariant_name: str,
                                    invariant_type: str, 
                                    task_name: str,
                                    model_name: str) -> Tuple[bool, str, str]:
        """
        Generate a .cfg file for a specific invariant by adding it to a base config.
        
        Args:
            tla_content: TLA+ specification content
            invariant_name: Name of the invariant to add
            invariant_type: Type of invariant ("safety" or "liveness")
            task_name: Task name for caching
            model_name: Model name for base config generation
            
        Returns:
            Tuple of (success, config_content, error_message)
        """
        try:
            # Get or generate base config
            base_config = self._get_base_config(tla_content, task_name, model_name)
            if not base_config:
                return False, "", "Failed to generate base config"
            
            # Add the specific invariant to the base config
            modified_config = self._add_invariant_to_config(
                base_config, invariant_name, invariant_type
            )
            
            return True, modified_config, None
            
        except Exception as e:
            logger.error(f"Static config generation failed: {e}")
            return False, "", str(e)
    
    def generate_config_for_invariant_from_base(self, 
                                               base_config: str,
                                               invariant_name: str,
                                               invariant_type: str) -> Tuple[bool, str, str]:
        """
        Generate a .cfg file for a specific invariant using an existing base config.
        This prevents cache pollution by not regenerating the base config.
        
        Args:
            base_config: Pre-generated base configuration
            invariant_name: Name of the invariant to add
            invariant_type: Type of invariant ("safety" or "liveness")
            
        Returns:
            Tuple of (success, config_content, error_message)
        """
        try:
            # Add the specific invariant to the provided base config
            modified_config = self._add_invariant_to_config(
                base_config, invariant_name, invariant_type
            )
            
            return True, modified_config, None
            
        except Exception as e:
            logger.error(f"Static config generation from base failed: {e}")
            return False, "", str(e)
    
    def _get_base_config(self, tla_content: str, task_name: str, model_name: str) -> Optional[str]:
        """
        Get base config, generating it once and caching.
        """
        if task_name in self.base_config_cache:
            logger.debug(f"Using cached base config for task: {task_name}")
            return self.base_config_cache[task_name]
        
        logger.info(f"Generating base config for task: {task_name}")
        
        # Generate base config with empty invariants using LLM
        # Use Claude for config generation as well since it produces better results
        claude_model_name = "claude"
        logger.info(f"Using Claude ({claude_model_name}) for base config generation (original model: {model_name})")
        success, config_content, error = self.llm_config_generator.generate_config(
            tla_content, "", task_name, claude_model_name
        )
        
        if success:
            self.base_config_cache[task_name] = config_content
            logger.info(f"Successfully cached base config for task: {task_name}")
            return config_content
        else:
            logger.error(f"Failed to generate base config: {error}")
            return None
    
    def _add_invariant_to_config(self, base_config: str, invariant_name: str, invariant_type: str) -> str:
        """
        Add a specific invariant to the base config based on its type.
        
        For safety invariants: add to INVARIANT section
        For liveness invariants: add to PROPERTY section
        """
        lines = base_config.split('\n')
        result_lines = []
        
        section_keyword = "INVARIANT" if invariant_type == "safety" else "PROPERTY"
        section_found = False
        invariant_added = False
        
        for i, line in enumerate(lines):
            result_lines.append(line)
            
            # Look for the target section
            if line.strip() == section_keyword:
                section_found = True
                # Add the invariant on the next line
                result_lines.append(f"    {invariant_name}")
                invariant_added = True
                logger.debug(f"Added {invariant_name} to existing {section_keyword} section")
        
        # If section not found, add it before the end of file
        if not section_found:
            # Find a good place to insert the section (typically after CONSTANTS)
            insert_index = len(result_lines)
            for i, line in enumerate(result_lines):
                if line.strip().startswith("CONSTANTS") or line.strip().startswith("SPECIFICATION"):
                    # Insert after this section
                    insert_index = i + 1
                    # Skip any content under this section
                    while (insert_index < len(result_lines) and 
                           result_lines[insert_index].strip() and
                           not result_lines[insert_index].strip().isupper()):
                        insert_index += 1
                    break
            
            # Insert the new section
            result_lines.insert(insert_index, "")
            result_lines.insert(insert_index + 1, section_keyword)
            result_lines.insert(insert_index + 2, f"    {invariant_name}")
            invariant_added = True
            logger.debug(f"Created new {section_keyword} section with {invariant_name}")
        
        if not invariant_added:
            logger.warning(f"Failed to add invariant {invariant_name} to config")
        
        return '\n'.join(result_lines)


class ManualInvariantEvaluator(BaseEvaluator):
    """
    Manual Invariant Evaluator: Phase 3 evaluation for TLA+ specifications.
    
    This evaluator implements the third phase of evaluation:
    1. Load expert-written invariant templates
    2. Translate templates to specific TLA+ specification (using Claude)
    3. Run TLC model checking for each invariant (using static .cfg generation)
    4. Report detailed results
    """
    
    def __init__(self, tlc_timeout: int = 60, templates_dir: str = "data/invariant_templates"):
        """
        Initialize manual invariant evaluator.
        
        Args:
            tlc_timeout: Timeout for TLC execution in seconds
            templates_dir: Directory containing invariant templates
        """
        super().__init__(timeout=tlc_timeout)
        self.template_loader = InvariantTemplateLoader(templates_dir)
        self.translator = InvariantTranslator()
        self.static_config_generator = StaticConfigGenerator()
        self.tlc_runner = TLCRunner(timeout=tlc_timeout)
    
    def evaluate(self, 
                generation_result: GenerationResult,
                task_name: str,
                method_name: str,
                model_name: str,
                spec_module: Optional[str] = None,
                base_config_content: Optional[str] = None,
                spec_file_path: Optional[str] = None,
                config_file_path: Optional[str] = None) -> SemanticEvaluationResult:
        """
        Evaluate a TLA+ specification using manual invariant testing.
        
        This method supports multiple modes:
        1. Composite mode: Reuse spec and config files from runtime check
        2. Standalone mode: Generate spec and config files independently
        
        Args:
            generation_result: GenerationResult containing the TLA+ specification
            task_name: Name of the task
            method_name: Name of the generation method
            model_name: Name of the model used
            spec_module: Optional TLA+ module name
            base_config_content: Optional pre-generated base config content to reuse
            spec_file_path: Optional path to existing .tla file (composite mode)
            config_file_path: Optional path to existing .cfg file (composite mode)
            
        Returns:
            SemanticEvaluationResult with manual invariant testing results
        """
        logger.info(f"Manual invariant evaluation: {task_name}/{method_name}/{model_name}")
        
        # Create structured output directory
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="invariant_verification",
            task=task_name,
            method=method_name,
            model=model_name
        )
        logger.info(f"Using output directory: {output_dir}")
        
        # Create evaluation result
        result = SemanticEvaluationResult(task_name, method_name, model_name)
        
        # Set generation time from the generation result metadata
        if hasattr(generation_result, 'metadata') and 'latency_seconds' in generation_result.metadata:
            result.generation_time = generation_result.metadata['latency_seconds']
        
        if not generation_result.success:
            result.invariant_generation_error = "Generation failed"
            result.overall_success = False
            return result
        
        # Determine working mode and prepare specification file
        if spec_file_path and Path(spec_file_path).exists():
            # Composite mode: Reuse existing spec file but copy to output directory
            logger.info(f"✓ Composite mode: Reusing existing spec file from runtime check: {spec_file_path}")
            
            # Read content from runtime check file
            with open(spec_file_path, 'r', encoding='utf-8') as f:
                tla_content = f.read()
            
            # Create copy in invariant verification output directory
            spec_file = output_dir / f"{spec_module or task_name}.tla"
            with open(spec_file, 'w', encoding='utf-8') as f:
                f.write(tla_content)
            result.specification_file = str(spec_file)
            logger.info(f"✓ Copied spec file to invariant verification directory: {spec_file}")
        else:
            # Standalone mode: Create new spec file
            logger.info("✓ Standalone mode: Creating new spec file")
            spec_file = output_dir / f"{spec_module or task_name}.tla"
            with open(spec_file, 'w', encoding='utf-8') as f:
                f.write(generation_result.generated_text)
            result.specification_file = str(spec_file)
            tla_content = generation_result.generated_text
        
        try:
            # Step 1: Load invariant templates
            logger.info("Step 1: Loading invariant templates...")
            templates = self.template_loader.load_task_invariants(task_name)
            
            # Step 2: Translate all invariants in one LLM call
            logger.info("Step 2: Translating invariants to specification...")
            translation_start = time.time()
            success, translated_invariants, error = self.translator.translate_all_invariants(
                templates, tla_content, task_name, model_name
            )
            
            result.invariant_generation_time = time.time() - translation_start
            result.invariant_generation_successful = success
            
            if not success:
                result.invariant_generation_error = error
                result.overall_success = False
                return result
            
            logger.info(f"Successfully translated {len(translated_invariants)} invariants")
            
            # Step 2.5: Get or generate clean base config
            if config_file_path and Path(config_file_path).exists():
                # Composite mode: Reuse existing config file and copy base config
                logger.info(f"Step 2.5: Using existing config file from runtime check: {config_file_path}")
                with open(config_file_path, 'r', encoding='utf-8') as f:
                    base_config = f.read()
                
                # Also save a copy of the base config to the invariant verification output directory
                base_config_file = output_dir / f"{spec_module or task_name}.cfg"
                with open(base_config_file, 'w', encoding='utf-8') as f:
                    f.write(base_config)
                logger.info(f"✓ Reusing config file from runtime check and copied to: {base_config_file}")
            elif base_config_content:
                # Use provided base config content
                logger.info("Step 2.5: Using provided base configuration content...")
                base_config = base_config_content
                logger.info("✓ Reusing base configuration content")
            else:
                # Standalone mode: Generate clean base config
                logger.info("Step 2.5: Generating clean base configuration...")
                base_config = self.static_config_generator._get_base_config(
                    tla_content,  # Use the appropriate TLA content
                    task_name, 
                    model_name
                )
                
                if not base_config:
                    logger.error("Failed to generate base configuration")
                    result.config_generation_error = "Failed to generate base configuration"
                    result.overall_success = False
                    return result
                
                logger.info("✓ Clean base configuration generated successfully")
            
            # Step 3: Test each invariant individually  
            logger.info("Step 3: Testing invariants with TLC...")
            invariant_results = []
            
            for i, template in enumerate(templates, 1):
                if template.name not in translated_invariants:
                    logger.warning(f"Invariant {template.name} was not translated, skipping")
                    continue
                
                logger.info(f"=== TESTING INVARIANT {i}/{len(templates)}: {template.name} ===")
                invariant_test_result = self._test_single_invariant(
                    template, translated_invariants[template.name],
                    tla_content, output_dir, spec_module or task_name,
                    task_name, model_name, base_config
                )
                
                # Print detailed results for each invariant test
                logger.info(f"INVARIANT {i} RESULT: {template.name}")
                logger.info(f"  Success: {invariant_test_result.success}")
                logger.info(f"  States explored: {invariant_test_result.states_explored}")
                logger.info(f"  Verification time: {invariant_test_result.verification_time:.2f}s")
                if invariant_test_result.error_message:
                    logger.info(f"  Error: {invariant_test_result.error_message}")
                logger.info(f"  Translated invariant: {invariant_test_result.translated_invariant}")
                logger.info(f"  TLC OUTPUT START ===")
                logger.info(invariant_test_result.tlc_output)
                logger.info(f"  TLC OUTPUT END ===")
                logger.info("")
                
                invariant_results.append(invariant_test_result)
            
            # Step 4: Aggregate results
            result.model_checking_successful = any(r.success for r in invariant_results)
            result.model_checking_time = sum(r.verification_time for r in invariant_results)
            
            # Set overall success - all invariants must pass
            passed_count = sum(1 for r in invariant_results if r.success)
            total_count = len(invariant_results)
            
            result.overall_success = (
                result.invariant_generation_successful and
                result.model_checking_successful and
                total_count > 0 and
                passed_count == total_count  # All invariants must pass
            )
            
            # Store detailed results
            result.custom_data = {
                "invariant_results": [
                    {
                        "name": r.name,
                        "success": r.success,
                        "states_explored": r.states_explored,
                        "verification_time": r.verification_time,
                        "error_message": r.error_message
                    }
                    for r in invariant_results
                ],
                "total_invariants": len(templates),
                "translated_invariants": len(translated_invariants),
                "passed_invariants": sum(1 for r in invariant_results if r.success),
                "failed_invariants": sum(1 for r in invariant_results if not r.success)
            }
            
            # Log detailed summary
            passed = result.custom_data["passed_invariants"] 
            total = len(invariant_results)
            
            logger.info("=== MANUAL INVARIANT VERIFICATION FINAL SUMMARY ===")
            logger.info(f"Total invariants tested: {total}")
            logger.info(f"Passed invariants: {passed}")
            logger.info(f"Failed invariants: {total - passed}")
            
            # List all results by name
            for i, inv_result in enumerate(invariant_results, 1):
                status = "✓ PASS" if inv_result.success else "✗ FAIL"
                logger.info(f"  {i}. {inv_result.name}: {status}")
            
            # Show final judgment logic
            logger.info(f"Invariant generation successful: {result.invariant_generation_successful}")
            logger.info(f"Model checking successful: {result.model_checking_successful}")
            logger.info(f"All invariants passed: {passed == total}")
            logger.info(f"Overall success: {result.overall_success}")
            logger.info(f"Manual invariant testing: {passed}/{total} invariants passed")
            
            return result
            
        except Exception as e:
            logger.error(f"Manual invariant evaluation failed: {e}")
            result.invariant_generation_error = str(e)
            result.overall_success = False
            return result
    
    def _test_single_invariant(self, 
                              template: InvariantTemplate,
                              translated_invariant: str, 
                              tla_content: str,
                              output_dir: Path,
                              spec_module: str,
                              task_name: str,
                              model_name: str,
                              base_config: str) -> InvariantTestResult:
        """Test a single invariant using TLC"""
        
        logger.debug(f"Testing invariant: {template.name}")
        
        try:
            # Create directory for this invariant
            invariant_dir = output_dir / template.name
            invariant_dir.mkdir(exist_ok=True)
            
            # Create modified TLA+ spec with the invariant
            modified_spec = self._add_invariant_to_spec(
                tla_content, translated_invariant, template.name
            )
            
            # Save modified spec with correct module name
            modified_spec_file = invariant_dir / f"{spec_module}.tla"
            with open(modified_spec_file, 'w', encoding='utf-8') as f:
                f.write(modified_spec)
            
            # Generate config file for this invariant using pre-generated clean base config
            # This prevents cache pollution from using modified_spec
            config_success, config_content, config_error = self.static_config_generator.generate_config_for_invariant_from_base(
                base_config, template.name, template.type
            )
            
            if not config_success:
                return InvariantTestResult(
                    name=template.name,
                    success=False,
                    translated_invariant=translated_invariant,
                    error_message=f"Config generation failed: {config_error}"
                )
            
            # Save config file with correct module name
            config_file = invariant_dir / f"{spec_module}.cfg"
            with open(config_file, 'w', encoding='utf-8') as f:
                f.write(config_content)
            
            # Run TLC (skip statistics recording for invariant checking, add -deadlock flag)
            start_time = time.time()
            tlc_success, tlc_output, tlc_exit_code = self.tlc_runner.run_model_checking(
                str(modified_spec_file), str(config_file), record_stats=False, use_deadlock_flag=True
            )
            verification_time = time.time() - start_time
            
            # Parse TLC results
            violations, deadlock_found, states_explored = self.tlc_runner.parse_tlc_output(tlc_output)
            
            success = tlc_success and len(violations) == 0 and not deadlock_found
            
            return InvariantTestResult(
                name=template.name,
                success=success,
                translated_invariant=translated_invariant,
                states_explored=states_explored,
                verification_time=verification_time,
                tlc_output=tlc_output,
                error_message=None if success else f"TLC failed: {len(violations)} violations, deadlock: {deadlock_found}"
            )
            
        except Exception as e:
            return InvariantTestResult(
                name=template.name,
                success=False,
                translated_invariant=translated_invariant,
                error_message=f"Testing failed: {str(e)}"
            )
    
    def _add_invariant_to_spec(self, tla_content: str, invariant_definition: str, invariant_name: str) -> str:
        """Add a single invariant definition to the TLA+ specification"""

        lines = tla_content.split('\n')
        result_lines = []

        # Find the insertion point (before the closing ====)
        invariant_inserted = False

        # Find the last occurrence of a line starting with ====
        last_separator_index = -1
        for i in range(len(lines) - 1, -1, -1):
            if lines[i].strip().startswith('===='):
                last_separator_index = i
                break

        for i, line in enumerate(lines):
            # Insert before the module closing separator
            if i == last_separator_index and last_separator_index != -1:
                if not invariant_inserted:
                    result_lines.append('')
                    result_lines.append(f'\\* Manual invariant: {invariant_name}')
                    result_lines.append(invariant_definition)
                    result_lines.append('')
                    invariant_inserted = True

            result_lines.append(line)

        # If no ==== found, append at the end
        if not invariant_inserted:
            result_lines.append('')
            result_lines.append(f'\\* Manual invariant: {invariant_name}')
            result_lines.append(invariant_definition)

        return '\n'.join(result_lines)
    
    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "semantic_invariant_verification"


# Convenience function for backward compatibility
def create_manual_invariant_evaluator(tlc_timeout: int = 60, 
                                     templates_dir: str = "data/invariant_templates") -> ManualInvariantEvaluator:
    """
    Factory function to create a manual invariant evaluator.
    
    Args:
        tlc_timeout: Timeout for TLC execution in seconds
        templates_dir: Directory containing invariant templates
        
    Returns:
        ManualInvariantEvaluator instance
    """
    return ManualInvariantEvaluator(tlc_timeout=tlc_timeout, templates_dir=templates_dir)