"""
Agent-based method implementation with automatic error correction.

This method generates TLA+ specifications and automatically detects and corrects
syntax and semantic errors using iterative LLM feedback.
"""

import logging
import time
from typing import Dict, Any, Optional, List, Tuple

from ..base import TLAGenerationMethod, GenerationTask, GenerationOutput, format_prompt_template
from ...config import get_configured_model
from ...core.verification.validators import TLAValidator, ValidationResult
from ...models.base import GenerationConfig

logger = logging.getLogger(__name__)


class AgentBasedMethod(TLAGenerationMethod):
    """
    Agent-based method for TLA+ generation with automatic error correction.
    
    This method implements a feedback loop:
    1. Generate initial TLA+ specification
    2. Validate syntax and semantics
    3. If errors found, provide error feedback to LLM for correction
    4. Repeat until specification is valid or max attempts reached
    """
    
    def __init__(self, max_correction_attempts: int = 3, validation_timeout: int = 30):
        """
        Initialize agent-based method.
        
        Args:
            max_correction_attempts: Maximum number of correction attempts
            validation_timeout: Timeout for TLA+ validation operations
        """
        super().__init__("agent_based")
        self.max_correction_attempts = max_correction_attempts
        self.validation_timeout = validation_timeout
        self.validator = TLAValidator(timeout=validation_timeout)
        
    def generate(self, task: GenerationTask, model_name: str = None) -> GenerationOutput:
        """
        Generate TLA+ specification with automatic error correction.
        
        Args:
            task: Generation task with source code
            model_name: Model to use from config
            
        Returns:
            GenerationOutput with corrected TLA+ specification
        """
        logger.info(f"Starting agent-based generation for task: {task.task_name}")
        
        try:
            # Get configured model
            model = get_configured_model(model_name)
            logger.info(f"Using model: {model.model_name}")
            
            # Step 1: Initial generation
            logger.info("Step 1: Initial TLA+ generation")
            initial_result = self._initial_generation(task, model)
            
            if not initial_result.success:
                logger.error(f"Initial generation failed: {initial_result.error_message}")
                return GenerationOutput(
                    tla_specification="",
                    method_name=self.name,
                    task_name=task.task_name,
                    metadata={"initial_generation_failed": True},
                    success=False,
                    error_message=initial_result.error_message
                )
            
            # Step 2: Validation and correction loop - COMMENTED OUT for composite evaluator
            # NOTE: Correction logic now handled by composite evaluator to avoid double-correction
            # This change allows composite evaluator to have full control over the correction process
            # logger.info("Step 2: Starting validation and correction loop")
            # final_result = self._correction_loop(
            #     task, initial_result.generated_text, model
            # )
            
            # Skip correction loop - return initial specification directly
            logger.info("Step 2: Skipping internal correction loop (composite evaluator will handle corrections)")
            
            # Compile metadata (no correction metadata)
            total_generation_time = initial_result.metadata.get('latency_seconds', 0)
            
            metadata = {
                "model_info": model.get_model_info(),
                "initial_generation_metadata": initial_result.metadata,
                "total_generation_time": total_generation_time,
                "method_type": "agent_based_no_internal_correction",
                "internal_correction_skipped": True
            }
            
            # Return initial specification without internal correction
            return GenerationOutput(
                tla_specification=initial_result.generated_text,
                method_name=self.name,
                task_name=task.task_name,
                metadata=metadata,
                success=True,
                error_message=None
            )
            
        except Exception as e:
            logger.error(f"Agent-based generation failed with exception: {e}")
            return GenerationOutput(
                tla_specification="",
                method_name=self.name,
                task_name=task.task_name,
                metadata={},
                success=False,
                error_message=str(e)
            )
    
    def _generate_correction(self, task, current_spec: str, all_errors: list, model_obj):
        """
        Generate correction for specification with errors (for composite evaluator).
        
        Args:
            task: Generation task
            current_spec: Current specification with errors
            all_errors: List of all errors to fix
            model_obj: Model object for correction
        
        Returns:
            GenerationResult with corrected specification
        """
        try:
            from ...core.verification.validators import ValidationResult
            
            # Convert error list to ValidationResult format
            validation_result = ValidationResult(
                success=False,
                output="Errors found by composite evaluator",
                syntax_errors=all_errors,
                semantic_errors=[],
                compilation_time=0.0
            )
            
            # Use existing correction method
            correction_result = self._attempt_correction(
                task, current_spec, validation_result, model_obj, 1
            )
            
            if correction_result['success']:
                from ...models.base import GenerationResult
                return GenerationResult(
                    generated_text=correction_result['corrected_specification'],
                    metadata=correction_result.get('correction_metadata', {}),
                    timestamp=time.time(),
                    success=True
                )
            else:
                from ...models.base import GenerationResult
                return GenerationResult(
                    generated_text=current_spec,
                    metadata={"correction_failed": True},
                    timestamp=time.time(),
                    success=False,
                    error_message=correction_result.get('error', 'Correction failed')
                )
                
        except Exception as e:
            logger.error(f"_generate_correction failed: {e}")
            from ...models.base import GenerationResult
            return GenerationResult(
                generated_text=current_spec,
                metadata={"correction_error": str(e)},
                timestamp=time.time(),
                success=False,
                error_message=f"Correction failed: {e}"
            )
    
    def _initial_generation(self, task: GenerationTask, model) -> Any:
        """Generate initial TLA+ specification using standard prompt."""
        prompt = self._create_initial_prompt(task)
        
        # Create generation config from model's YAML configuration
        generation_config = GenerationConfig(
            max_tokens=model.config.get('max_tokens'),
            temperature=model.config.get('temperature'),
            top_p=model.config.get('top_p')  # Only if defined in YAML
        )
        
        logger.info(f"Initial generation config from YAML: {model.config}")
        logger.debug(f"Using initial prompt ({len(prompt)} chars)")
        return model.generate_tla_specification(task.source_code, prompt, generation_config)
    
    def _correction_loop(self, task: GenerationTask, initial_spec: str, model) -> Dict[str, Any]:
        """
        Perform validation and correction loop.
        
        Args:
            task: Generation task
            initial_spec: Initial TLA+ specification
            model: LLM model for correction
            
        Returns:
            Dictionary with final specification and correction metadata
        """
        current_spec = initial_spec
        correction_attempts = 0
        correction_history = []
        total_correction_time = 0.0
        
        while correction_attempts < self.max_correction_attempts:
            logger.info(f"Validation attempt {correction_attempts + 1}/{self.max_correction_attempts}")
            
            # Validate current specification (with language support)
            validation_start = time.time()
            validation_result = self._validate_specification(
                current_spec,
                task.spec_module,
                task.spec_language
            )
            validation_time = time.time() - validation_start
            
            logger.info(f"Validation completed in {validation_time:.2f}s: {'✓ PASS' if validation_result.success else '✗ FAIL'}")
            
            if validation_result.success:
                # Specification is valid, we're done
                logger.info("✓ Specification validation successful, no correction needed")
                return {
                    'success': True,
                    'final_specification': current_spec,
                    'correction_attempts': correction_attempts,
                    'correction_history': correction_history,
                    'total_correction_time': total_correction_time,
                    'final_validation_result': validation_result
                }
            
            # Specification has errors, print detailed error information
            logger.error(f"✗ Validation failed with {len(validation_result.syntax_errors)} syntax errors and {len(validation_result.semantic_errors)} semantic errors")
            
            if validation_result.syntax_errors:
                logger.error("Syntax errors:")
                for i, error in enumerate(validation_result.syntax_errors[:5]):  # Show first 5 errors
                    logger.error(f"  {i+1}. {error}")
                if len(validation_result.syntax_errors) > 5:
                    logger.error(f"  ... and {len(validation_result.syntax_errors) - 5} more syntax errors")
            
            if validation_result.semantic_errors:
                logger.error("Semantic errors:")
                for i, error in enumerate(validation_result.semantic_errors[:5]):  # Show first 5 errors
                    logger.error(f"  {i+1}. {error}")
                if len(validation_result.semantic_errors) > 5:
                    logger.error(f"  ... and {len(validation_result.semantic_errors) - 5} more semantic errors")
            
            # Print complete validation output for debugging in early development phase
            if validation_result.output:
                logger.error("=== COMPLETE VALIDATION OUTPUT FOR DEBUGGING ===")
                logger.error(validation_result.output)  # Print entire output
                logger.error("=== END COMPLETE VALIDATION OUTPUT ===")
                
            
            # Attempt correction
            logger.info(f"✗ Attempting correction (attempt {correction_attempts + 1})")
            
            correction_start = time.time()
            correction_result = self._attempt_correction(
                task, current_spec, validation_result, model, correction_attempts + 1
            )
            correction_time = time.time() - correction_start
            total_correction_time += correction_time
            
            if not correction_result['success']:
                logger.error(f"Correction attempt {correction_attempts + 1} failed: {correction_result['error']}")
                break
            
            # Update specification with corrected version
            current_spec = correction_result['corrected_specification']
            correction_attempts += 1
            
            # Record correction history
            correction_history.append({
                'attempt': correction_attempts,
                'original_errors': self._extract_error_summary(validation_result),
                'correction_time': correction_time,
                'correction_success': True
            })
            
            logger.info(f"Correction attempt {correction_attempts} completed in {correction_time:.2f}s")
        
        # Max attempts reached without success
        logger.warning(f"Maximum correction attempts ({self.max_correction_attempts}) reached")

        # Final validation to get current error state
        final_validation = self._validate_specification(
            current_spec,
            task.spec_module,
            task.spec_language
        )
        
        # Print final error summary
        logger.error("=== FINAL VALIDATION ERRORS AFTER ALL CORRECTION ATTEMPTS ===")
        logger.error(f"Final result: {len(final_validation.syntax_errors)} syntax errors, {len(final_validation.semantic_errors)} semantic errors")
        
        if final_validation.syntax_errors:
            logger.error("Final syntax errors:")
            for i, error in enumerate(final_validation.syntax_errors[:5]):
                logger.error(f"  {i+1}. {error}")
            if len(final_validation.syntax_errors) > 5:
                logger.error(f"  ... and {len(final_validation.syntax_errors) - 5} more syntax errors")
        
        if final_validation.semantic_errors:
            logger.error("Final semantic errors:")
            for i, error in enumerate(final_validation.semantic_errors[:5]):
                logger.error(f"  {i+1}. {error}")
            if len(final_validation.semantic_errors) > 5:
                logger.error(f"  ... and {len(final_validation.semantic_errors) - 5} more semantic errors")
        
        # Print complete final validation output for debugging
        if final_validation.output:
            logger.error("=== COMPLETE FINAL VALIDATION OUTPUT FOR DEBUGGING ===")
            logger.error(final_validation.output)  # Print entire output
            logger.error("=== END COMPLETE FINAL VALIDATION OUTPUT ===")
            
            # Final specification content removed - too verbose for normal output
        
        logger.error("=== END FINAL VALIDATION ERRORS ===")
        
        return {
            'success': False,
            'final_specification': current_spec,
            'correction_attempts': correction_attempts,
            'correction_history': correction_history,
            'total_correction_time': total_correction_time,
            'final_validation_result': final_validation,
            'error_message': f"Failed to correct specification after {correction_attempts} attempts"
        }
    
    def _validate_specification(self, specification: str, module_name: Optional[str] = None,
                              spec_language: str = "tla") -> ValidationResult:
        """
        Validate specification for syntax and basic semantic errors (multi-language support).

        Args:
            specification: Specification content
            module_name: Optional module name
            spec_language: Specification language (tla, alloy, etc.)

        Returns:
            ValidationResult with validation outcome
        """
        try:
            import tempfile
            import os
            from pathlib import Path
            from ...core.verification.validator_factory import get_validator

            # Create temporary directory for validation
            temp_dir = Path(tempfile.mkdtemp())

            try:
                # Get appropriate validator for language
                validator = get_validator(spec_language, self.validation_timeout)

                if spec_language.lower() == "alloy":
                    # Alloy validation
                    if not module_name:
                        module_name = "temp_spec"

                    temp_file_path = temp_dir / f"{module_name}.als"
                    temp_file_path.write_text(specification, encoding='utf-8')

                    # AlloyValidator.validate() expects spec_content and output_dir
                    result = validator.validate(specification, temp_dir)

                    logger.debug(f"Alloy validation result: success={result.success}, "
                                f"syntax_errors={len(result.syntax_errors)}, "
                                f"semantic_errors={len(result.semantic_errors)}")

                    return result

                else:
                    # TLA+ validation
                    if not module_name:
                        raise ValueError("Module name is required for TLA+ validation but was not provided")

                    temp_file_path = temp_dir / f"{module_name}.tla"
                    temp_file_path.write_text(specification, encoding='utf-8')

                    # TLAValidator - call internal validation directly
                    from ...core.verification.validators import TLAValidator
                    success, output = validator._run_sany_validation(str(temp_file_path))

                    # Parse errors from output
                    syntax_errors, semantic_errors = validator._parse_errors(output) if not success else ([], [])

                    # Create ValidationResult object
                    result = ValidationResult(
                        success=success,
                        output=output,
                        syntax_errors=syntax_errors,
                        semantic_errors=semantic_errors,
                        compilation_time=0.0
                    )

                    logger.debug(f"TLA+ validation result: success={result.success}, "
                                f"syntax_errors={len(result.syntax_errors)}, "
                                f"semantic_errors={len(result.semantic_errors)}")

                    return result

            finally:
                # Clean up temporary directory
                import shutil
                try:
                    shutil.rmtree(temp_dir)
                except:
                    pass

        except Exception as e:
            logger.error(f"Validation failed with exception: {e}")
            return ValidationResult(
                success=False,
                output=f"Validation exception: {e}",
                syntax_errors=[str(e)],
                semantic_errors=[],
                compilation_time=0.0
            )
    
    def _attempt_correction(self, task: GenerationTask, current_spec: str, 
                          validation_result: ValidationResult, model, attempt_num: int) -> Dict[str, Any]:
        """
        Attempt to correct errors in the specification using LLM feedback.
        
        Args:
            task: Original generation task
            current_spec: Current specification with errors
            validation_result: Validation result containing errors
            model: LLM model for correction
            attempt_num: Current attempt number
            
        Returns:
            Dictionary with correction result
        """
        try:
            # Create correction prompt with error feedback
            correction_prompt = self._create_correction_prompt(
                task, current_spec, validation_result, attempt_num
            )
            
            logger.debug(f"Correction prompt created ({len(correction_prompt)} chars)")
            
            # Create generation config from model's YAML configuration
            generation_config = GenerationConfig(
                max_tokens=model.config.get('max_tokens'),
                temperature=model.config.get('temperature'),
                top_p=model.config.get('top_p')  # Only if defined in YAML
            )
            
            logger.info(f"Correction generation config from YAML, attempt={attempt_num}")
            
            # Generate corrected specification (no source code needed for correction)
            correction_result = model.generate_tla_specification(
                "", 
                correction_prompt,
                generation_config
            )
            
            if not correction_result.success:
                return {
                    'success': False,
                    'error': correction_result.error_message,
                    'corrected_specification': current_spec
                }
            
            return {
                'success': True,
                'corrected_specification': correction_result.generated_text,
                'correction_metadata': correction_result.metadata
            }
            
        except Exception as e:
            logger.error(f"Correction attempt failed: {e}")
            return {
                'success': False,
                'error': str(e),
                'corrected_specification': current_spec
            }
    
    def _create_initial_prompt(self, task: GenerationTask) -> str:
        """Create initial generation prompt (multi-language support)."""
        # Get task-specific prompt template (same as direct_call method)
        # Use spec_language to select language-specific prompt
        from ...tasks.loader import get_task_loader
        task_loader = get_task_loader()
        prompt_template = task_loader.get_task_prompt(
            task.task_name,
            "agent_based",  # Use agent_based prompt for initial generation
            task.spec_language  # Language-specific prompt
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

        # Format template with task information (without escaping literal braces)
        return format_prompt_template(prompt_template, format_vars)
    
    def _create_correction_prompt(self, task: GenerationTask, current_spec: str, 
                                validation_result: ValidationResult, attempt_num: int) -> str:
        """
        Create correction prompt with error feedback.
        
        Args:
            task: Original generation task
            current_spec: Current specification with errors
            validation_result: Validation errors
            attempt_num: Current correction attempt number
            
        Returns:
            Formatted correction prompt
        """
        # Get agent-based correction prompt template (language-specific)
        from ...tasks.loader import get_task_loader
        task_loader = get_task_loader()

        try:
            correction_template = task_loader.get_task_prompt(
                task.task_name,
                "agent_correction",  # Use correction-specific prompt
                task.spec_language  # Language-specific
            )
        except Exception:
            # Fallback to a default correction prompt if task-specific one doesn't exist
            logger.warning(f"No agent_correction prompt found for task {task.task_name}/{task.spec_language}, using default correction prompt")
            correction_template = self._get_default_correction_prompt(task.spec_language)
        
        # Extract error information
        error_summary = self._extract_error_summary(validation_result)
        
        # Prepare format variables - escape any problematic characters
        def safe_format(text):
            """Safely format text to avoid string formatting issues."""
            if text is None:
                return "None"
            # Replace problematic characters that might break string formatting  
            return str(text).replace('{', '{{').replace('}', '}}')
        
        format_vars = {
            'language': safe_format(task.language),
            'description': safe_format(task.description),
            'system_type': safe_format(task.system_type),
            'current_specification': safe_format(current_spec),
            'error_summary': safe_format(error_summary),
            'syntax_errors': safe_format('\n'.join(validation_result.syntax_errors) if validation_result.syntax_errors else "None"),
            'semantic_errors': safe_format('\n'.join(validation_result.semantic_errors) if validation_result.semantic_errors else "None"),
            'attempt_number': attempt_num,
            'max_attempts': self.max_correction_attempts,
            'validation_output': safe_format(validation_result.output)
        }
        
        # Add extra info if available
        if task.extra_info:
            for key, value in task.extra_info.items():
                format_vars[key] = safe_format(value)
        
        try:
            return correction_template.format(**format_vars)
        except Exception as e:
            logger.error(f"Error formatting correction prompt: {e}")
            logger.debug(f"Format variables: {format_vars}")
            raise
    
    def _extract_error_summary(self, validation_result: ValidationResult) -> str:
        """Extract a concise error summary from validation result."""
        errors = []
        
        if validation_result.syntax_errors:
            errors.append(f"Syntax errors ({len(validation_result.syntax_errors)}): " + 
                         "; ".join(validation_result.syntax_errors[:3]))  # First 3 errors
            if len(validation_result.syntax_errors) > 3:
                errors.append(f"... and {len(validation_result.syntax_errors) - 3} more syntax errors")
        
        if validation_result.semantic_errors:
            errors.append(f"Semantic errors ({len(validation_result.semantic_errors)}): " + 
                         "; ".join(validation_result.semantic_errors[:3]))  # First 3 errors
            if len(validation_result.semantic_errors) > 3:
                errors.append(f"... and {len(validation_result.semantic_errors) - 3} more semantic errors")
        
        return "\n".join(errors) if errors else "No specific errors identified"
    
    def _get_default_correction_prompt(self, spec_language: str = "tla") -> str:
        """Default correction prompt template when task-specific prompt is not available."""
        language_name = "TLA+" if spec_language.lower() == "tla" else spec_language.upper()

        return f"""You are an expert in {language_name} specification language. I need you to fix errors in a {language_name} specification.

Original task: Create a {language_name} specification for a {{system_type}} system.

Description: {{description}}

Current {language_name} specification (with errors):
```
{{current_specification}}
```

Validation errors found:
{{error_summary}}

Detailed syntax errors:
{{syntax_errors}}

Detailed semantic errors:
{{semantic_errors}}

This is correction attempt {{attempt_number}} of {{max_attempts}}.

Please provide a corrected {language_name} specification that fixes these errors. Focus on:
1. Fixing syntax errors (missing operators, incorrect syntax)
2. Resolving semantic errors (undefined variables, incorrect logic)
3. Maintaining the original intent and structure where possible
4. Ensuring the specification is valid {language_name}

Return only the corrected {language_name} specification without explanations."""
    
    def get_method_info(self) -> Dict[str, Any]:
        """Get information about agent-based method."""
        return {
            "name": self.name,
            "description": "Agent-based LLM generation with automatic error correction",
            "type": "iterative_correction",
            "requires_model": True,
            "supports_iteration": True,
            "max_correction_attempts": self.max_correction_attempts,
            "validation_timeout": self.validation_timeout,
            "features": [
                "automatic_error_detection",
                "iterative_correction",
                "syntax_validation",
                "semantic_validation"
            ]
        }
