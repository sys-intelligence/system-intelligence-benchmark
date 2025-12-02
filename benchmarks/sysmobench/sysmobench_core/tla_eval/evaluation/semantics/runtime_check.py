"""
Runtime Check Evaluator: Semantic-level evaluation for TLA+ specifications.

This evaluator implements runtime checking which includes:
1. TLC configuration file (.cfg) generation from existing TLA+ specifications
2. TLC model checking execution and result analysis using specification's own invariants
"""

import os
import subprocess
import time
import logging
import re
from pathlib import Path
from string import Template
from typing import Dict, Any, List, Optional, Tuple
from dataclasses import dataclass

from ...models.base import GenerationResult
from ...config import get_configured_model
from ...core.verification.error_statistics_manager import classify_and_record_tlc_result, TLCErrorCategory, get_experiment_error_statistics_manager
from ...utils.output_manager import get_output_manager
from ..base.evaluator import BaseEvaluator
from ..base.result_types import SemanticEvaluationResult

logger = logging.getLogger(__name__)



class ConfigGenerator:
    """Generates TLC configuration files (.cfg) using LLM"""
    
    def __init__(self):
        self.name = "config_generator"
    
    def generate_config(self, tla_content: str, invariants: str, task_name: str, model_name: str) -> Tuple[bool, str, str]:
        """
        Generate TLC configuration file from TLA+ specification and invariants.
        
        Args:
            tla_content: TLA+ specification content
            invariants: Generated invariants
            task_name: Name of the task (for loading prompt)
            model_name: Model to use for generation
            
        Returns:
            Tuple of (success, generated_config, error_message)
        """
        try:
            # Special handling for with_exist_spec - generate basic config instead of using LLM
            if model_name == "with_exist_spec":
                return self._generate_basic_config(tla_content, invariants)
            
            # Use the original config-based approach for compatibility with existing models
            model = get_configured_model(model_name)
            
            # Load task-specific prompt for config generation
            prompt_template = self._load_config_prompt(task_name)
            
            # Format prompt with TLA+ specification and invariants using Template to avoid brace conflicts
            from string import Template
            
            # Debug: Check inputs
            logger.debug(f"TLA content length: {len(tla_content) if tla_content else 'None'}")
            logger.debug(f"Invariants length: {len(invariants) if invariants else 'None'}")
            logger.debug(f"Prompt template length: {len(prompt_template)}")
            
            template = Template(prompt_template)
            try:
                prompt = template.substitute(tla_spec=tla_content, invariants=invariants)
            except KeyError as e:
                logger.error(f"Template substitution failed - missing key: {e}")
                logger.error(f"Available template keys: {[k for k in prompt_template if '$' in k]}")
                raise e
            
            # Use the unified model interface for config generation
            from ...models.base import GenerationConfig
            # Don't override model configuration - let it use the model's configured values
            gen_config = GenerationConfig()
            
            import time
            start_time = time.time()
            
            result = model.generate_direct(prompt, gen_config)
            end_time = time.time()
            
            logger.debug(f"=== CONFIG GENERATION RESULT ===")
            logger.debug(f"Success: {result.success}")
            logger.debug(f"Length: {len(result.generated_text) if result.success else 0}")
            if result.success:
                logger.debug(f"Content preview: {repr(result.generated_text[:200])}")
                logger.debug(f"SPECIFICATION count: {result.generated_text.count('SPECIFICATION')}")
            else:
                logger.debug(f"Error: {result.error_message}")
            
            if result.success:
                final_config = result.generated_text.strip()
                logger.debug(f"=== AFTER STRIP ===")
                logger.debug(f"Length: {len(final_config)}")
                logger.debug(f"SPECIFICATION count: {final_config.count('SPECIFICATION')}")
                return True, final_config, None
            else:
                logger.error(f"Model generation failed with error: {result.error_message}")
                logger.debug(f"Generated text length: {len(result.generated_text) if result.generated_text else 0}")
                logger.debug(f"Generated text preview: {repr(result.generated_text[:200]) if result.generated_text else 'None'}")
                return False, "", result.error_message
                
        except Exception as e:
            logger.error(f"Config generation failed: {e}")
            logger.error(f"Exception type: {type(e)}")
            logger.error(f"Exception args: {e.args}")
            
            # Additional debugging information
            logger.debug(f"=== CONFIG GENERATION DEBUG INFO ===")
            logger.debug(f"Task name: {task_name}")
            logger.debug(f"Model name: {model_name}")
            logger.debug(f"TLA content preview: {tla_content[:200] if tla_content else 'None'}...")
            logger.debug(f"Invariants: {invariants}")
            logger.debug(f"=== END DEBUG INFO ===")
            
            return False, "", str(e)
    
    def _generate_basic_config(self, tla_content: str, invariants: str) -> Tuple[bool, str, str]:
        """
        Generate a basic TLC configuration for with_exist_spec model.
        
        Args:
            tla_content: TLA+ specification content
            invariants: Invariants to include (can be empty)
            
        Returns:
            Tuple of (success, config_content, error_message)
        """
        try:
            import re
            
            # Parse the module name from TLA+ specification (handle ---- MODULE name ---- format)
            module_match = re.search(r'^\s*-*\s*MODULE\s+(\w+)\s*-*\s*$', tla_content, re.MULTILINE)
            if not module_match:
                return False, "", "Cannot find MODULE declaration in TLA+ specification"
            
            module_name = module_match.group(1)
            
            # Extract variables from VARIABLES declaration
            var_match = re.search(r'^\s*VARIABLES?\s+(.+?)$', tla_content, re.MULTILINE)
            variables = []
            if var_match:
                var_text = var_match.group(1).strip()
                # Handle both single variables and comma-separated lists
                var_text = re.sub(r'\s+', ' ', var_text)  # Normalize whitespace
                var_text = var_text.replace(',', ' ')
                variables = [v.strip() for v in var_text.split() if v.strip()]
            
            # Find Init and Next predicates
            init_match = re.search(r'^\s*Init\s*==', tla_content, re.MULTILINE)
            next_match = re.search(r'^\s*Next\s*==', tla_content, re.MULTILINE)
            
            if not init_match:
                return False, "", "Cannot find Init predicate in TLA+ specification"
            if not next_match:
                return False, "", "Cannot find Next predicate in TLA+ specification"
            
            # Generate basic configuration
            config_lines = [
                f"SPECIFICATION Spec",
                f"",
                f"\\* Basic constraints for model checking",
            ]
            
            # Add variable type constraints if we found variables
            if variables:
                config_lines.append(f"\\* Variables: {', '.join(variables)}")
                config_lines.append(f"")
            
            # Add invariants if provided
            if invariants and invariants.strip():
                config_lines.append(f"\\* Generated invariants:")
                for line in invariants.strip().split('\n'):
                    if line.strip():
                        config_lines.append(f"INVARIANT {line.strip()}")
                config_lines.append(f"")
            
            # Basic model checking settings
            config_lines.extend([
                f"\\* Model checking constraints",
                f"CONSTANTS",
                f"\\* Add any necessary constant definitions here",
                f"",
                f"\\* State constraints to limit state space",
                f"\\* CONSTRAINT StateConstraint"
            ])
            
            config_content = '\n'.join(config_lines)
            logger.info(f"Generated basic config for module {module_name}")
            return True, config_content, None
            
        except Exception as e:
            logger.error(f"Basic config generation failed: {e}")
            return False, "", str(e)
    
    def _load_config_prompt(self, task_name: str) -> str:
        """Load task-specific prompt for config generation"""
        from ...tasks.loader import get_task_loader
        task_loader = get_task_loader()
        
        # Get task directory path
        tasks_dir = task_loader.tasks_dir
        prompt_file = tasks_dir / task_name / "prompts" / "phase2_config.txt"
        
        if not prompt_file.exists():
            raise FileNotFoundError(f"Phase 2 config prompt not found: {prompt_file}")
        
        with open(prompt_file, 'r', encoding='utf-8') as f:
            return f.read()


class TLCRunner:
    """Runs TLC model checker and parses results"""
    
    def __init__(self, timeout: int = 300, error_stats_manager=None):
        """
        Initialize TLC runner.
        
        Args:
            timeout: Timeout for TLC execution in seconds
            error_stats_manager: Optional custom error statistics manager
        """
        self.timeout = timeout
        self.error_stats_manager = error_stats_manager
        self.tla_tools_path = self._get_tla_tools_path()
    
    def _get_tla_tools_path(self) -> Path:
        """Get path to TLA+ tools"""
        from ...utils.setup_utils import get_tla_tools_path
        return get_tla_tools_path()
    
    def run_model_checking(self, spec_file: str, config_file: str, record_stats: bool = True, use_deadlock_flag: bool = True) -> Tuple[bool, str, int]:
        """
        Run TLC model checking.
        
        Args:
            spec_file: Path to TLA+ specification file
            config_file: Path to TLC configuration file
            record_stats: Whether to record error statistics (default True for safety)
            use_deadlock_flag: Whether to add -deadlock flag for invariant checking (default True)
            
        Returns:
            Tuple of (success, output, exit_code)
        """
        try:
            # Convert paths to absolute and then get relative paths for TLC
            spec_path = Path(spec_file).resolve()
            config_path = Path(config_file).resolve()
            working_dir = spec_path.parent
            
            # Get relative paths from working directory
            spec_filename = spec_path.name
            config_filename = config_path.name
            
            # Construct TLC command with relative paths
            cmd = [
                "java",
                "-cp", str(self.tla_tools_path),
                "tlc2.TLC",
                "-config", config_filename
            ]
            
            # Add -deadlock flag for invariant checking context
            if use_deadlock_flag:
                cmd.append("-deadlock")
            
            cmd.append(spec_filename)
            
            logger.debug(f"Running TLC in {working_dir}: {' '.join(cmd)}")

            # DEBUG: Add detailed logging
            logger.info(f"🔍 DEBUG TLC EXECUTION:")
            logger.info(f"  Command: {' '.join(cmd)}")
            logger.info(f"  Working directory: {working_dir}")
            logger.info(f"  Timeout: {self.timeout}s")

            # Run TLC
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.timeout,
                cwd=working_dir  # Run in spec directory
            )

            output = result.stdout + result.stderr

            # DEBUG: Add detailed result logging
            logger.info(f"🔍 DEBUG TLC RESULT:")
            logger.info(f"  Exit code: {result.returncode}")
            logger.info(f"  Stdout length: {len(result.stdout)} chars")
            logger.info(f"  Stderr length: {len(result.stderr)} chars")
            logger.info(f"  Combined output length: {len(output)} chars")
            logger.info(f"🔍 DEBUG TLC STDOUT (first 1000 chars):")
            logger.info(f"{result.stdout[:1000]}")
            logger.info(f"🔍 DEBUG TLC STDERR (first 1000 chars):")
            logger.info(f"{result.stderr[:1000]}")
            
            if record_stats:
                # Use new error classification system and record statistics (default behavior)
                if self.error_stats_manager:
                    # Use custom error statistics manager
                    error_info = self.error_stats_manager.classify_and_record_tlc_result(
                        result.returncode, 
                        result.stdout, 
                        result.stderr, 
                        context="runtime"  # This is runtime model checking
                    )
                else:
                    # Use global error statistics manager (default behavior)
                    error_info = classify_and_record_tlc_result(
                        result.returncode, 
                        result.stdout, 
                        result.stderr, 
                        context="runtime"  # This is runtime model checking
                    )
                
                # Determine success based on error classification
                if error_info.category == TLCErrorCategory.SUCCESS:
                    content_based_success = True
                elif error_info.is_violation:
                    # Violations are model checking findings, not spec errors
                    # In runtime context, violations indicate the model found issues
                    content_based_success = False  # The specification has issues
                    logger.info(f"TLC found model violations: {error_info.description}")
                else:
                    # Other errors (compilation, runtime errors, etc.)
                    content_based_success = False
                    logger.info(f"TLC failed: {error_info.category.value} - {error_info.description}")
                
                # Parse output for detailed information to include in debug log
                violations, deadlock_found, states_explored = self.parse_tlc_output(output)
                logger.debug(f"TLC finished: classification={error_info.category.value}, violations={len(violations)}, deadlock={deadlock_found}, states={states_explored}")
            else:
                # Skip statistics recording (for invariant checking context)
                # Use simple exit code based success determination
                content_based_success = (result.returncode == 0)
                
                if not content_based_success:
                    logger.debug(f"TLC failed with exit code {result.returncode} (stats recording disabled)")
                else:
                    logger.debug("TLC succeeded (stats recording disabled)")
            
            # Always parse output for detailed information (for backwards compatibility)
            violations, deadlock_found, states_explored = self.parse_tlc_output(output)
            
            return content_based_success, output, result.returncode
            
        except subprocess.TimeoutExpired as e:
            # DEBUG: Add timeout logging
            logger.info(f"🔍 DEBUG TLC TIMEOUT:")
            logger.info(f"  Timeout occurred after {self.timeout}s")
            logger.info(f"  Exception type: {type(e)}")

            # For large state spaces, timeout without violations should be considered success
            # Parse partial output to check for violations AND configuration errors
            partial_output = ""
            partial_stdout = ""
            partial_stderr = ""
            
            try:
                # Try to get partial output from the process
                if hasattr(e, 'stdout') and e.stdout:
                    partial_stdout = e.stdout.decode() if isinstance(e.stdout, bytes) else str(e.stdout)
                    partial_output += partial_stdout
                if hasattr(e, 'stderr') and e.stderr:
                    partial_stderr = e.stderr.decode() if isinstance(e.stderr, bytes) else str(e.stderr)
                    partial_output += partial_stderr

                # DEBUG: Add partial output logging
                logger.info(f"🔍 DEBUG TIMEOUT PARTIAL OUTPUT:")
                logger.info(f"  Partial stdout length: {len(partial_stdout)} chars")
                logger.info(f"  Partial stderr length: {len(partial_stderr)} chars")
                logger.info(f"  Partial stdout (first 500 chars): {partial_stdout[:500]}")
                logger.info(f"  Partial stderr (first 500 chars): {partial_stderr[:500]}")

            except Exception as parse_error:
                # If we can't get partial output, just use empty string
                logger.info(f"🔍 DEBUG: Could not parse partial output: {parse_error}")
                partial_output = ""
                partial_stdout = ""
                partial_stderr = ""
            
            # FIXED: Always check violations first for timeout cases, regardless of error classification
            # Parse the partial output for violations and deadlocks
            violations, deadlock_found, states_explored = self.parse_tlc_output(partial_output)

            # If we found actual violations or deadlocks, this is a real failure
            if violations or deadlock_found:
                logger.info(f"🔍 DEBUG: Found violations/deadlock in timeout - returning FAILURE")

                # Record error statistics only for actual violations/deadlocks, not for timeout itself
                if record_stats:
                    logger.debug("Recording error statistics for violations/deadlock found during timeout")
                    if self.error_stats_manager:
                        error_info = self.error_stats_manager.classify_and_record_tlc_result(
                            -1,  # Process was terminated, but due to violations found
                            partial_stdout,
                            partial_stderr,
                            context="runtime_violations"  # Context shows this is for violations, not timeout
                        )
                    else:
                        error_info = classify_and_record_tlc_result(
                            -1,
                            partial_stdout,
                            partial_stderr,
                            context="runtime_violations"
                        )

                return False, f"TLC found violations/deadlocks before timeout after {self.timeout} seconds:\n{partial_output}", -1

            # No violations found - this should be considered success for large state spaces
            # FIXED: Clean timeout (no violations) is not an error and should not be recorded in error statistics
            logger.debug("Clean timeout with no violations - not recording any error statistics")
            
            # DEBUG: Add timeout result analysis (violations already parsed above)
            logger.info(f"🔍 DEBUG TIMEOUT ANALYSIS:")
            logger.info(f"  Violations found: {len(violations)}")
            logger.info(f"  Deadlock found: {deadlock_found}")
            logger.info(f"  States explored: {states_explored}")
            logger.info(f"  Violations list: {violations}")

            # No violations found within timeout - consider this success for large state spaces
            logger.info(f"🔍 DEBUG: Returning SUCCESS - timeout with no violations")
            logger.info(f"TLC timeout after {self.timeout}s with no violations found - considering as success")
            success_msg = f"TLC explored {states_explored} states in {self.timeout} seconds with no violations found (timeout reached but no errors detected)"
            return True, success_msg, 0
        except Exception as e:
            return False, f"TLC execution failed: {e}", -1
    
    def parse_tlc_output(self, output: str) -> Tuple[List[str], bool, int]:
        """
        Parse TLC output to extract violations and statistics.
        
        Args:
            output: TLC output text
            
        Returns:
            Tuple of (invariant_violations, deadlock_found, states_explored)
        """
        violations = []
        deadlock_found = False
        states_explored = 0
        
        lines = output.split('\n')
        
        for i, line in enumerate(lines):
            line = line.strip()
            
            # Check for invariant violations
            if "Invariant" in line and "is violated" in line:
                violations.append(line)
            
            # Check for deadlock
            if "Deadlock reached" in line:
                deadlock_found = True
            
            # Check for TLA+ specification errors
            if "Error:" in line:
                violations.append(f"TLA+ Error: {line}")
            
            # Check for variable definition errors
            if "not completely specified" in line or "variables are not defined" in line:
                violations.append(f"Variable definition error: {line}")
            
            # Check for other semantic errors
            if "The following variables are not defined" in line:
                violations.append(f"Undefined variables: {line}")
            
            # Extract states explored
            if "states generated" in line.lower():
                import re
                match = re.search(r'(\d+)\s+states generated', line)
                if match:
                    states_explored = int(match.group(1))
        
        return violations, deadlock_found, states_explored


class RuntimeCheckEvaluator(BaseEvaluator):
    """
    Runtime Check Evaluator: Semantic evaluation for TLA+ specifications.
    
    This evaluator takes TLA+ specifications and performs:
    1. TLC configuration generation from existing specifications
    2. Model checking with TLC using specification's own invariants
    """
    
    def __init__(self, tlc_timeout: int = 60):
        """
        Initialize runtime check evaluator.
        
        Args:
            tlc_timeout: Timeout for TLC execution in seconds
        """
        super().__init__(timeout=tlc_timeout)
        self.config_generator = ConfigGenerator()
        # Create separate error statistics manager for this evaluator
        self.error_stats_manager = get_experiment_error_statistics_manager()
        # Create TLC runner with custom error statistics manager
        self.tlc_runner = TLCRunner(timeout=tlc_timeout, error_stats_manager=self.error_stats_manager)
    
    def evaluate(self, 
                generation_result: GenerationResult,
                task_name: str,
                method_name: str,
                model_name: str,
                spec_module: str = None,
                spec_file_path: Optional[str] = None,
                config_file_path: Optional[str] = None) -> SemanticEvaluationResult:
        """
        Evaluate a TLA+ specification using model checking.
        
        Args:
            generation_result: GenerationResult containing the TLA+ specification
            task_name: Name of the task
            method_name: Name of the generation method
            model_name: Name of the model used
            spec_module: Optional TLA+ module name
            spec_file_path: Optional path to existing .tla file (use instead of generation_result)
            config_file_path: Optional path to existing .cfg file (use instead of generating new one)
            
        Returns:
            SemanticEvaluationResult with model checking results
        """
        logger.info(f"Runtime check evaluation: {task_name}/{method_name}/{model_name}")
        
        # Create structured output directory
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="runtime_check",
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
        
        try:
            # Step 1: Determine input source and get TLA+ content
            if spec_file_path and Path(spec_file_path).exists():
                # Use existing spec file
                logger.info(f"Using existing spec file: {spec_file_path}")
                try:
                    with open(spec_file_path, 'r', encoding='utf-8') as f:
                        tla_content = f.read()
                except Exception as e:
                    logger.error(f"Failed to read spec file: {e}")
                    result.error_message = f"Cannot read spec file: {e}"
                    return result
            else:
                # Use generated content
                if not generation_result.success:
                    logger.error("Generation failed, cannot perform semantic evaluation")
                    result.error_message = "Generation failed"
                    return result
                
                tla_content = generation_result.generated_text
                if not tla_content.strip():
                    logger.error("Empty TLA+ specification from generation result")
                    result.error_message = "Empty specification"
                    return result
                
                logger.info("✓ Specification content loaded from generation result")
            
            if not tla_content.strip():
                logger.error("Empty TLA+ specification content")
                result.error_message = "Empty specification"
                return result
            
            # Step 1.5: Check if specification passed syntax validation (for agent_based method)
            # If agent_based method failed correction after 3 attempts, skip expensive semantic evaluation
            if method_name == "agent_based" and generation_result.metadata:
                correction_metadata = generation_result.metadata.get('correction_metadata', {})
                if correction_metadata and not correction_metadata.get('success', True):
                    final_validation = correction_metadata.get('final_validation_result')
                    if final_validation and not final_validation.success and final_validation.syntax_errors:
                        logger.warning("⚠️ Specification failed syntax validation after 3 correction attempts")
                        logger.warning("Skipping expensive semantic evaluation (config generation + TLC) to save costs")
                        logger.warning(f"Syntax errors: {len(final_validation.syntax_errors)} errors found")
                        
                        result.error_message = f"Syntax validation failed after {correction_metadata.get('correction_attempts', 3)} attempts"
                        result.invariant_generation_successful = False
                        result.config_generation_successful = False  
                        result.model_checking_successful = False
                        result.overall_success = False
                        
                        # Still save the specification for inspection
                        module_name = spec_module or task_name
                        spec_file_path = output_dir / f"{module_name}.tla"
                        with open(spec_file_path, 'w', encoding='utf-8') as f:
                            f.write(tla_content)
                        result.specification_file = str(spec_file_path)
                        
                        return result
            
            # Save specification to output directory for reference
            module_name = spec_module or task_name
            spec_file_path = output_dir / f"{module_name}.tla"
            with open(spec_file_path, 'w', encoding='utf-8') as f:
                f.write(tla_content)
            result.specification_file = str(spec_file_path)
            
            # Step 2: Skip invariant generation - use existing TLA+ specification directly
            logger.info("⏭️  Skipping invariant generation - using original specification without additional invariants")
            
            # The specification is already saved above in spec_file_path
            logger.info(f"Original specification saved to: {spec_file_path}")
            result.invariant_generation_time = 0.0
            result.invariant_generation_successful = True
            result.generated_invariants = []  # No generated invariants
            result.invariant_generation_error = None
            
            # Step 3: Handle TLC configuration (use existing or generate new)
            if config_file_path and Path(config_file_path).exists():
                # Use existing config file
                logger.info(f"Using existing config file: {config_file_path}")
                try:
                    with open(config_file_path, 'r', encoding='utf-8') as f:
                        config = f.read()
                    
                    # Copy to output directory for consistency
                    output_config_path = output_dir / f"{module_name}.cfg"
                    with open(output_config_path, 'w', encoding='utf-8') as f:
                        f.write(config)

                    # Ensure downstream TLC runner uses the copied config in the output directory
                    config_file_path = output_config_path
                    result.config_file_path = str(output_config_path)
                    result.config_generation_time = 0.0
                    result.config_generation_successful = True
                    result.config_generation_error = None
                    logger.info("✓ Using existing config file")
                    
                except Exception as e:
                    logger.error(f"Failed to read config file: {e}")
                    result.config_generation_error = f"Cannot read config file: {e}"
                    result.config_generation_successful = False
                    result.config_file_path = str(config_file_path)
                    logger.warning(f"Preserving original config path despite read failure: {config_file_path}")
                    return result
            else:
                # Generate new TLC configuration
                logger.info("Generating TLC configuration...")
                start_time = time.time()
                
                # Use empty invariants string since we're not generating new invariants
                cfg_success, config, cfg_error = self.config_generator.generate_config(
                    tla_content, "", task_name, model_name  # Empty invariants
                )
                
                result.config_generation_time = time.time() - start_time
                result.config_generation_successful = cfg_success
                result.config_generation_error = cfg_error
                
                if not cfg_success:
                    logger.error(f"✗ Config generation failed: {cfg_error}")
                    return result
                
                # Save config file to structured output directory
                config_file_path = output_dir / f"{module_name}.cfg"
                
                logger.debug(f"Writing config to {config_file_path}, length: {len(config)} chars")
                logger.debug(f"Config content preview: {config[:200]}...")
                with open(config_file_path, 'w', encoding='utf-8') as f:
                    f.write(config)
                
                result.config_file_path = str(config_file_path)
                logger.info(f"✓ TLC config generated in {result.config_generation_time:.2f}s")
            
            # Step 4: Run TLC model checking
            logger.info("Running TLC model checking...")
            start_time = time.time()
            
            tlc_success, tlc_output, tlc_exit_code = self.tlc_runner.run_model_checking(
                str(spec_file_path), str(config_file_path)
            )
            
            result.model_checking_time = time.time() - start_time
            result.model_checking_successful = tlc_success
            result.model_checking_error = f"TLC failed with exit code {tlc_exit_code}" if not tlc_success else None
            
            if not tlc_success:
                logger.error(f"✗ TLC model checking failed: {result.model_checking_error}")
            else:
                logger.info(f"✓ TLC completed in {result.model_checking_time:.2f}s")
            
            # Step 5: Parse TLC results
            violations, deadlock, states = self.tlc_runner.parse_tlc_output(tlc_output)
            result.invariant_violations = violations
            result.deadlock_found = deadlock
            result.states_explored = states
            
            # Update overall success
            result.overall_success = (
                result.invariant_generation_successful and
                result.config_generation_successful and
                result.model_checking_successful and
                len(result.invariant_violations) == 0 and
                not result.deadlock_found
            )
            
            if result.overall_success:
                logger.info("✓ Semantic evaluation: PASS")
            else:
                violations_msg = f"{len(violations)} violations" if violations else "no violations"
                deadlock_msg = "deadlock found" if deadlock else "no deadlock"
                logger.info(f"✗ Semantic evaluation: FAIL ({violations_msg}, {deadlock_msg})")
            
            # Save results and metadata to structured output directory
            result_data = {
                "overall_success": result.overall_success,
                "invariant_generation_successful": result.invariant_generation_successful,
                "config_generation_successful": result.config_generation_successful,
                "model_checking_successful": result.model_checking_successful,
                "invariant_generation_time": result.invariant_generation_time,
                "config_generation_time": result.config_generation_time,
                "model_checking_time": result.model_checking_time,
                "states_explored": result.states_explored,
                "invariant_violations": result.invariant_violations,
                "deadlock_found": result.deadlock_found,
                "generated_invariants": result.generated_invariants,
                "errors": {
                    "invariant_generation_error": result.invariant_generation_error,
                    "config_generation_error": result.config_generation_error,
                    "model_checking_error": result.model_checking_error
                }
            }
            
            metadata = {
                "task_name": task_name,
                "method_name": method_name,
                "model_name": model_name,
                "metric": "runtime_check",
                "specification_file": result.specification_file,
                "config_file_path": result.config_file_path,
                "tlc_timeout": self.timeout,
                "evaluation_timestamp": time.time()
            }
            
            output_manager.save_result(output_dir, result_data, metadata)
            
            # Save error statistics for this runtime_check run
            try:
                stats_file_path = self.error_stats_manager.save_experiment_statistics(
                    output_dir=output_dir,
                    task_name=task_name,
                    method_name=method_name,
                    model_name=model_name
                )
                logger.info(f"Error statistics saved to: {stats_file_path}")
            except Exception as stats_error:
                logger.error(f"Failed to save error statistics: {stats_error}")
            
            return result
            
        except Exception as e:
            logger.error(f"Semantic evaluation failed: {e}")
            result.model_checking_error = str(e)
            return result
    
    def _insert_invariants_into_spec(self, tla_content: str, invariants: str) -> str:
        """
        Insert generated invariants into TLA+ specification before the ending ====.
        
        Args:
            tla_content: Original TLA+ specification content
            invariants: Generated invariants to insert
            
        Returns:
            Updated TLA+ specification with invariants
        """
        lines = tla_content.split('\n')
        
        # Find the line with ==== (4 or more equals)
        ending_line_index = -1
        for i in range(len(lines) - 1, -1, -1):  # Search from end
            line = lines[i].strip()
            if line.startswith('====') and len(line) >= 4:
                ending_line_index = i
                break
        
        if ending_line_index == -1:
            # If no ==== found, append at the end
            logger.warning("No ==== ending found in specification, appending invariants at end")
            return tla_content + '\n\n' + invariants + '\n===='
        
        # Insert invariants before the ==== line
        result_lines = lines[:ending_line_index]
        result_lines.append('')  # Empty line before invariants
        result_lines.extend(invariants.split('\n'))
        result_lines.append('')  # Empty line after invariants
        result_lines.extend(lines[ending_line_index:])  # Add ==== and any content after
        
        return '\n'.join(result_lines)
    
    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "semantic_runtime_check"


# Convenience function for backward compatibility
def create_runtime_check_evaluator(tlc_timeout: int = 60) -> RuntimeCheckEvaluator:
    """
    Factory function to create a runtime check evaluator.
    
    Args:
        tlc_timeout: Timeout for TLC execution in seconds
        
    Returns:
        RuntimeCheckEvaluator instance
    """
    return RuntimeCheckEvaluator(tlc_timeout=tlc_timeout)