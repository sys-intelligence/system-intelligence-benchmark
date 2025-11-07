"""
Action Decomposition Evaluator: Syntax-level evaluation for TLA+ action decomposition.

This evaluator implements action-level syntax validation by:
1. Generating TLA+ specifications using LLM
2. Decomposing the specification into individual actions
3. Creating standalone TLA+ files for each action
4. Validating syntax of each action individually using SANY
5. Collecting comprehensive statistics on action-level syntax correctness
"""

import os
import re
import tempfile
import shutil
import logging
import time
from pathlib import Path
from typing import Dict, List, Any, Tuple, Optional
from dataclasses import dataclass

from ...core.verification.validators import TLAValidator, ValidationResult
from ...core.verification.error_statistics_manager import get_experiment_error_statistics_manager
from ...models.base import GenerationResult
from ...utils.output_manager import get_output_manager
from ..base.evaluator import BaseEvaluator
from ..base.result_types import SyntaxEvaluationResult

logger = logging.getLogger(__name__)


@dataclass
class ActionValidationResult:
    """Result of validating a single action"""
    action_name: str
    file_path: str
    validation_result: ValidationResult
    variables_added: List[str]
    functions_added: List[str]
    recovery_attempts: int


class ActionDecompositionEvaluator(BaseEvaluator):
    """
    Evaluator for TLA+ action decomposition and individual action syntax validation.
    
    This evaluator decomposes TLA+ specifications into individual actions and validates
    each action's syntax separately, providing detailed insights into which specific
    actions have syntax issues.
    """
    
    def __init__(self, validation_timeout: int = 30, keep_temp_files: bool = False):
        """
        Initialize action decomposition evaluator.
        
        Args:
            validation_timeout: Timeout for TLA+ validation in seconds
            keep_temp_files: Whether to keep temporary action files for debugging
        """
        super().__init__(timeout=validation_timeout)
        self.keep_temp_files = keep_temp_files
        self.temp_dir = None
        # Create separate error statistics manager for this evaluator
        self.error_stats_manager = get_experiment_error_statistics_manager()
        # Create validator with custom error statistics manager
        self.validator = TLAValidator(timeout=validation_timeout, error_stats_manager=self.error_stats_manager)
    
    def evaluate(self, 
                generation_result: GenerationResult,
                task_name: str,
                method_name: str,
                model_name: str,
                spec_module: str = None,
                spec_file_path: Optional[str] = None,
                config_file_path: Optional[str] = None) -> SyntaxEvaluationResult:
        """
        Evaluate a generation result using action decomposition.
        
        Args:
            generation_result: Result from TLA+ generation
            task_name: Name of the task
            method_name: Name of the generation method
            model_name: Name of the model used
            spec_module: Optional TLA+ module name for the specification
            spec_file_path: Optional path to existing .tla file (use instead of generation_result)
            config_file_path: Optional path to existing .cfg file (unused but kept for interface consistency)
            
        Returns:
            SyntaxEvaluationResult with detailed action-level evaluation metrics
        """
        logger.info(f"Evaluating action decomposition: {task_name}/{method_name}/{model_name}")
        
        # Create evaluation result
        eval_result = SyntaxEvaluationResult(task_name, method_name, model_name)
        self._set_generation_result(eval_result, generation_result)
        
        # Determine input source and get TLA+ content
        if spec_file_path and Path(spec_file_path).exists():
            # Use existing spec file
            logger.info(f"Using existing spec file: {spec_file_path}")
            try:
                with open(spec_file_path, 'r', encoding='utf-8') as f:
                    tla_content = f.read()
            except Exception as e:
                logger.error(f"Failed to read spec file: {e}")
                validation_result = ValidationResult(
                    success=False,
                    output=f"Failed to read spec file: {e}",
                    syntax_errors=[f"Cannot read spec file: {e}"],
                    semantic_errors=[],
                    compilation_time=0.0
                )
                self._set_validation_result(eval_result, validation_result)
                return eval_result
        else:
            # Use generated content
            if not generation_result.success:
                logger.warning(f"Generation failed, cannot proceed: {generation_result.error_message}")
                validation_result = ValidationResult(
                    success=False,
                    output="Generation failed - no specification to validate",
                    syntax_errors=[],
                    semantic_errors=["Generation failed"],
                    compilation_time=0.0
                )
                self._set_validation_result(eval_result, validation_result)
                return eval_result
            tla_content = generation_result.generated_text
        
        # Set the actual content being evaluated (may be from file or generation)
        eval_result.generated_specification = tla_content
        
        try:
            # Create temporary directory for action files
            self.temp_dir = Path(tempfile.mkdtemp(prefix="tla_action_decomp_"))
            logger.debug(f"Created temporary directory: {self.temp_dir}")
            
            # Step 1: Decompose specification into actions
            logger.debug("Starting action decomposition...")
            actions = self._decompose_specification(tla_content)
            logger.info(f"Decomposed specification into {len(actions)} actions")
            
            # Step 2: Create standalone TLA+ files for each action
            action_results = []
            successful_count = 0
            
            for i, (action_name, action_content) in enumerate(actions.items(), 1):
                logger.info(f"Processing action {i}/{len(actions)}: {action_name}")
                action_result = self._validate_action(action_name, action_content, spec_module or "ActionModule", task_name)
                action_results.append(action_result)
                
                if action_result.validation_result.success:
                    successful_count += 1
                    logger.info(f"  ✓ Action '{action_name}' validated successfully")
                else:
                    error_count = len(action_result.validation_result.syntax_errors) + len(action_result.validation_result.semantic_errors)
                    logger.warning(f"  ✗ Action '{action_name}' failed validation ({error_count} errors)")
            
            logger.info(f"Action validation progress: {successful_count}/{len(actions)} actions successful so far")
            
            # Step 3: Aggregate results
            self._aggregate_action_results(eval_result, action_results)
            
            # Step 4: Overall validation of original specification
            logger.debug("Validating original specification...")
            overall_validation = self.validator.validate_specification(
                tla_content,
                module_name=spec_module,
                task_name=task_name,
                context="action_decomposition"
            )
            self._set_validation_result(eval_result, overall_validation)
            
            logger.info(f"Action decomposition complete: {len(action_results)} actions evaluated")
            
        except Exception as e:
            logger.error(f"Action decomposition evaluation error: {e}")
            validation_result = ValidationResult(
                success=False,
                output=f"Action decomposition error: {e}",
                syntax_errors=[],
                semantic_errors=[str(e)],
                compilation_time=0.0
            )
            self._set_validation_result(eval_result, validation_result)
        
        finally:
            # Save results to output directory
            try:
                output_manager = get_output_manager()
                output_dir = output_manager.create_experiment_dir(
                    metric="action_decomposition",
                    task=task_name,
                    method=method_name,
                    model=model_name
                )
                
                # Prepare result data
                result_data = {
                    "overall_success": eval_result.overall_success,
                    "generation_successful": eval_result.generation_successful,
                    "compilation_successful": eval_result.compilation_successful,
                    "generation_time": eval_result.generation_time,
                    "compilation_time": eval_result.compilation_time,
                    "total_actions": getattr(eval_result, 'total_actions', 0),
                    "successful_actions": getattr(eval_result, 'successful_actions', 0),
                    "action_success_rate": getattr(eval_result, 'action_success_rate', 0.0),
                    "total_variables_added": getattr(eval_result, 'total_variables_added', 0),
                    "total_functions_added": getattr(eval_result, 'total_functions_added', 0),
                    "total_recovery_attempts": getattr(eval_result, 'total_recovery_attempts', 0),
                    "syntax_errors": eval_result.syntax_errors,
                    "semantic_errors": eval_result.semantic_errors,
                    "action_results": [
                        {
                            "action_name": ar.action_name,
                            "success": ar.validation_result.success,
                            "compilation_time": ar.validation_result.compilation_time,
                            "syntax_errors": ar.validation_result.syntax_errors,
                            "semantic_errors": ar.validation_result.semantic_errors,
                            "variables_added": ar.variables_added,
                            "functions_added": ar.functions_added,
                            "recovery_attempts": ar.recovery_attempts
                        } for ar in getattr(eval_result, 'action_results', [])
                    ]
                }
                
                metadata = {
                    "task_name": task_name,
                    "method_name": method_name,
                    "model_name": model_name,
                    "metric": "action_decomposition",
                    "evaluation_timestamp": time.time(),
                    "validation_timeout": self.timeout,
                    "keep_temp_files": self.keep_temp_files
                }
                
                # Save specification to output directory
                if eval_result.generated_specification:
                    spec_file_path = output_dir / f"{spec_module or 'specification'}.tla"
                    with open(spec_file_path, 'w', encoding='utf-8') as f:
                        f.write(eval_result.generated_specification)
                    metadata["specification_file"] = str(spec_file_path)
                
                output_manager.save_result(output_dir, result_data, metadata)
                logger.info(f"Results saved to: {output_dir}")
                
                # Save error statistics for this action_decomposition run
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
                
                # Store output directory path in evaluation result for display
                eval_result.output_directory = str(output_dir)
                
            except Exception as save_error:
                logger.error(f"Failed to save results: {save_error}")
            
            # Cleanup temporary files unless keeping them
            if self.temp_dir and not self.keep_temp_files:
                try:
                    shutil.rmtree(self.temp_dir)
                    logger.debug("Cleaned up temporary directory")
                except Exception as e:
                    logger.warning(f"Failed to cleanup temporary directory: {e}")
        
        logger.info(f"Evaluation complete: success={eval_result.overall_success}")
        return eval_result
    
    def _count_function_arguments(self, args_str: str) -> int:
        """
        Count function arguments, properly handling nested parentheses and brackets.
        
        For example:
        - "a, b, c" -> 3 arguments
        - "[x |-> 1, y |-> 2], b" -> 2 arguments (record + simple arg)
        - "" -> 0 arguments
        """
        if not args_str.strip():
            return 0
        
        # Track nesting levels for different bracket types
        paren_level = 0
        bracket_level = 0
        brace_level = 0
        
        arg_count = 1  # Start with 1, will become 0 if we find no real content
        in_arg = False
        
        for char in args_str:
            if char == '(':
                paren_level += 1
                in_arg = True
            elif char == ')':
                paren_level -= 1
                in_arg = True
            elif char == '[':
                bracket_level += 1
                in_arg = True
            elif char == ']':
                bracket_level -= 1
                in_arg = True
            elif char == '{':
                brace_level += 1
                in_arg = True
            elif char == '}':
                brace_level -= 1
                in_arg = True
            elif char == ',' and paren_level == 0 and bracket_level == 0 and brace_level == 0:
                # This is a top-level comma, so we have another argument
                arg_count += 1
            elif not char.isspace():
                in_arg = True
        
        # If we never found any real content, return 0
        return arg_count if in_arg else 0
    
    def _decompose_specification(self, tla_content: str) -> Dict[str, str]:
        """
        Decompose TLA+ specification into individual actions.
        
        Args:
            tla_content: Complete TLA+ specification content
            
        Returns:
            Dictionary mapping action names to their content
        """
        actions = {}
        lines = tla_content.split('\n')
        
        # Pattern to match action definitions: ActionName(params) == body
        # Must start at beginning of line (no indentation)
        action_pattern = re.compile(r'^([A-Za-z_][A-Za-z0-9_]*)\s*(\([^)]*\))?\s*==(.*)$')
        
        current_action = None
        current_action_lines = []
        
        i = 0
        while i < len(lines):
            line = lines[i]
            line_stripped = line.strip()
            
            # Skip empty lines and comments
            if not line_stripped or line_stripped.startswith('\\*'):
                if current_action:
                    current_action_lines.append(line)
                i += 1
                continue
            
            # Check if this line starts a new action (must have no leading whitespace)
            if not line.startswith(' ') and not line.startswith('\t'):
                match = action_pattern.match(line_stripped)
                if match:
                    # Save previous action if exists
                    if current_action and current_action_lines:
                        actions[current_action] = '\n'.join(current_action_lines).strip()
                    
                    # Start new action
                    action_name = match.group(1)
                    params = match.group(2) or ""
                    body = match.group(3).strip()
                    
                    current_action = action_name
                    current_action_lines = [line]  # Keep original formatting
                    
                    # Continue reading the action until we find the next non-indented line
                    # or reach end of file
                    i += 1
                    while i < len(lines):
                        next_line = lines[i]
                        next_line_stripped = next_line.strip()
                        
                        # If we hit an empty line or comment, include it
                        if not next_line_stripped or next_line_stripped.startswith('\\*'):
                            current_action_lines.append(next_line)
                            i += 1
                            continue
                        
                        # If we hit a non-indented line that's not a comment, this action is done
                        if not next_line.startswith(' ') and not next_line.startswith('\t'):
                            # Check if it's the start of another action or module boundary
                            if (next_line_stripped.startswith('----') or 
                                next_line_stripped.startswith('====') or
                                next_line_stripped.startswith('EXTENDS') or
                                next_line_stripped.startswith('CONSTANTS') or
                                next_line_stripped.startswith('VARIABLES') or
                                next_line_stripped.startswith('ASSUME') or
                                action_pattern.match(next_line_stripped)):
                                break
                        
                        # This line is part of the current action
                        current_action_lines.append(next_line)
                        i += 1
                    
                    logger.debug(f"Found action: {action_name} ({len(current_action_lines)} lines)")
                    continue
            
            # If we're not in an action and this is a non-indented line, skip it
            if not current_action:
                i += 1
                continue
            
            # This shouldn't happen with the new logic, but keep as fallback
            current_action_lines.append(line)
            i += 1
        
        # Save last action if exists
        if current_action and current_action_lines:
            actions[current_action] = '\n'.join(current_action_lines).strip()
        
        # Filter out empty actions
        actions = {name: content for name, content in actions.items() if content.strip()}
        
        logger.debug(f"Decomposed into {len(actions)} actions: {list(actions.keys())}")
        return actions
    
    def _validate_action(self, action_name: str, action_content: str, base_module: str, task_name: str = None) -> ActionValidationResult:
        """
        Validate a single action by creating a standalone TLA+ file.
        
        Args:
            action_name: Name of the action
            action_content: Content of the action
            base_module: Base module name for the action file
            task_name: Name of the task (for action name extraction)

        Returns:
            ActionValidationResult with validation outcome
        """
        module_name = f"{base_module}_{action_name}"
        action_file = self.temp_dir / f"{module_name}.tla"
        
        variables_added = []
        functions_added = []
        recovery_attempts = 0
        
        try:
            # Create initial TLA+ file for the action
            tla_content = self._create_action_file_content(module_name, action_content)
            
            with open(action_file, 'w', encoding='utf-8') as f:
                f.write(tla_content)
            
            # Validate and attempt error recovery
            validation_result = self.validator.validate_file(str(action_file), context="action_decomposition")
            
            # Attempt to fix common errors
            if not validation_result.success:
                recovery_attempts += 1
                logger.debug(f"Attempting error recovery for action: {action_name}")
                
                # Try to add missing variables first (original order)
                added_vars = self._add_missing_variables(str(action_file))
                variables_added.extend(added_vars)
                
                # Try to add missing functions, and remove any variables that are actually functions
                added_funcs = self._add_missing_functions(str(action_file), added_variables=added_vars, task_name=task_name)
                functions_added.extend(added_funcs)
                
                # Re-validate after fixes
                if added_vars or added_funcs:
                    validation_result = self.validator.validate_file(str(action_file), context="action_decomposition")
                    if not validation_result.success:
                        recovery_attempts += 1
            
            # Final validation to record error statistics (after all fixes are complete)
            final_validation_result = self.validator.validate_file(str(action_file), context="action_validation")
            logger.debug(f"Final validation for action {action_name}: success={final_validation_result.success}")
            
            return ActionValidationResult(
                action_name=action_name,
                file_path=str(action_file),
                validation_result=final_validation_result,
                variables_added=variables_added,
                functions_added=functions_added,
                recovery_attempts=recovery_attempts
            )
            
        except Exception as e:
            logger.error(f"Error validating action {action_name}: {e}")
            error_result = ValidationResult(
                success=False,
                output=f"Action validation error: {e}",
                syntax_errors=[str(e)],
                semantic_errors=[],
                compilation_time=0.0
            )
            return ActionValidationResult(
                action_name=action_name,
                file_path=str(action_file) if action_file else "",
                validation_result=error_result,
                variables_added=variables_added,
                functions_added=functions_added,
                recovery_attempts=recovery_attempts
            )
    
    def _create_action_file_content(self, module_name: str, action_content: str) -> str:
        """
        Create complete TLA+ file content for a single action.
        
        Args:
            module_name: Name of the TLA+ module
            action_content: Content of the action
            
        Returns:
            Complete TLA+ file content
        """
        content_lines = [
            f"---- MODULE {module_name} ----",
            "EXTENDS TLC, Sequences, Bags, FiniteSets, Integers, Naturals",
            "",
            action_content,
            "",
            "====",
            ""
        ]
        
        return '\n'.join(content_lines)
    
    def _add_missing_variables(self, file_path: str) -> List[str]:
        """
        Add missing variables detected from SANY output.
        
        Args:
            file_path: Path to the TLA+ file
            
        Returns:
            List of variables that were added
        """
        # Run SANY to get error output
        validation_result = self.validator.validate_file(file_path, context="action_decomposition")
        output = validation_result.output
        
        # Extract unknown operators that might be variables
        pattern = r"Unknown operator: `([^']*)'."
        matches = re.findall(pattern, output)
        
        if not matches:
            return []
        
        # Read current file content to analyze usage patterns
        with open(file_path, 'r', encoding='utf-8') as f:
            file_content = f.read()
        
        # Distinguish between variables and functions based on usage
        actual_variables = []
        potential_functions = []
        
        for op in set(matches):
            # Check if this operator is used with parentheses (function call)
            function_usage = re.search(rf'\b{re.escape(op)}\s*\(', file_content)
            # Check if it's used without parentheses (variable access)
            variable_usage = re.search(rf'\b{re.escape(op)}\s*(?!\()', file_content)
            
            if function_usage and not variable_usage:
                # Used only as function
                potential_functions.append(op)
            elif variable_usage:
                # Used as variable (may also be used as function)
                actual_variables.append(op)
            else:
                # Unknown usage pattern, default to variable
                actual_variables.append(op)
        
        if actual_variables:
            logger.debug(f"Adding variables: {actual_variables}")
            logger.debug(f"Skipping function-like operators: {potential_functions}")
            
            # Read current file content
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            
            # Find insertion point (after EXTENDS line)
            insert_idx = 2
            for i, line in enumerate(lines):
                if line.startswith("EXTENDS"):
                    insert_idx = i + 1
                    break
            
            # Check if VARIABLES already exists
            var_line_idx = None
            for i, line in enumerate(lines):
                if line.startswith("VARIABLES"):
                    var_line_idx = i
                    break
            
            if var_line_idx is None:
                # Add new VARIABLES declaration
                var_declaration = f"VARIABLES {', '.join(actual_variables)}\n"
                lines.insert(insert_idx, var_declaration)
                lines.insert(insert_idx + 1, "\n")  # Add empty line
            else:
                # Update existing VARIABLES line
                existing_vars = lines[var_line_idx].replace("VARIABLES", "").strip()
                if existing_vars:
                    existing_list = [v.strip() for v in existing_vars.split(",")]
                    all_vars = existing_list + actual_variables
                else:
                    all_vars = actual_variables
                
                # Remove duplicates while preserving order
                unique_vars = []
                for v in all_vars:
                    if v and v not in unique_vars:
                        unique_vars.append(v)
                
                lines[var_line_idx] = f"VARIABLES {', '.join(unique_vars)}\n"
            
            # Write back to file
            with open(file_path, 'w', encoding='utf-8') as f:
                f.writelines(lines)
        
        return actual_variables
    
    def _add_missing_functions(self, file_path: str, added_variables: List[str] = None, task_name: str = None) -> List[str]:
        """
        Add missing function definitions detected from SANY output using iterative approach.
        This method will run multiple iterations, detecting and adding new Unknown operators
        that appear after initial fixes until no more Unknown operators are found.
        
        Args:
            file_path: Path to the TLA+ file
            added_variables: List of variables already added (will remove these if they're actually functions)
            task_name: Name of the task (used for extracting action names from file paths)

        Returns:
            List of functions that were added across all iterations
        """
        if added_variables is None:
            added_variables = []
        all_added_funcs = []
        variables_to_remove = []  # Track variables that should be removed because they're actually functions
        max_iterations = 5
        
        for iteration in range(max_iterations):
            # print(f"DEBUG: Starting iteration {iteration + 1}")
            
            # Run SANY to get error output
            validation_result = self.validator.validate_file(file_path, context="action_decomposition")
            output = validation_result.output
            
            # Extract functions that require specific number of arguments
            pattern = r"The operator ([^\s]*) requires (\d+) argument"
            matches = re.findall(pattern, output)
            
            # Also look for "Unknown operator" that are used as functions
            unknown_pattern = r"Unknown operator: `([^']*)'."
            unknown_ops = re.findall(unknown_pattern, output)
            
            # print(f"DEBUG: Iteration {iteration + 1}: Found explicit function requirements: {matches}")
            # print(f"DEBUG: Iteration {iteration + 1}: Found unknown operators: {unknown_ops}")
            
            # If no new operators found, we're done
            if not matches and not unknown_ops:
                # print(f"DEBUG: No more unknown operators found after {iteration + 1} iterations")
                break
            
            # Read current file content
            with open(file_path, 'r', encoding='utf-8') as f:
                file_content = f.read()
                lines = file_content.split('\n')
            
            iteration_added_funcs = []
            functions_to_add = []
            
            # Process explicit function requirements
            for func_name, arg_count in matches:
                # Skip if already added in previous iterations
                if func_name in all_added_funcs:
                    # print(f"DEBUG: Skipping {func_name} (already added in previous iteration)")
                    continue
                    
                arg_count = int(arg_count)
                
                # Determine correct arity by analyzing usage in the file
                func_calls = re.findall(rf'\b{re.escape(func_name)}\s*\([^)]*\)', file_content)
                if func_calls:
                    # Count arguments in the first function call, handling nested brackets/parentheses
                    first_call = func_calls[0]
                    args_part = first_call[first_call.find('(')+1:first_call.rfind(')')]
                    actual_arg_count = self._count_function_arguments(args_part)
                else:
                    actual_arg_count = arg_count
                
                if actual_arg_count == 0:
                    func_def = f"{func_name} == TRUE"
                else:
                    params = ", ".join([f"x{i+1}" for i in range(actual_arg_count)])
                    func_def = f"{func_name}({params}) == TRUE"
                
                # print(f"DEBUG: Iteration {iteration + 1}: Will add function: {func_def}")
                functions_to_add.append(func_def)
                iteration_added_funcs.append(func_name)
                
                # If this operator was previously added as a variable, mark it for removal
                if func_name in added_variables:
                    variables_to_remove.append(func_name)
                    # print(f"DEBUG: Marking {func_name} for removal from VARIABLES (it's actually a function)")
            
            # Process all unknown operators - always add them if not already added
            for op in set(unknown_ops):
                # print(f"DEBUG: Iteration {iteration + 1}: Processing unknown operator: {op}")
                
                # Skip if already processed in previous iterations
                if op in all_added_funcs:
                    # print(f"DEBUG: Skipping {op} (already added in previous iteration)")
                    continue
                    
                # Check if this is used as a function
                function_usage = re.findall(rf'\b{re.escape(op)}\s*\([^)]*\)', file_content)
                # print(f"DEBUG: Function usage found for {op}: {function_usage}")
                
                if function_usage:
                    # Add as function
                    first_usage = function_usage[0]
                    args_part = first_usage[first_usage.find('(')+1:first_usage.rfind(')')]
                    arg_count = self._count_function_arguments(args_part)
                    # print(f"DEBUG: Determined arg_count={arg_count} for {op} from '{args_part}'")
                    
                    if arg_count == 0:
                        func_def = f"{op} == TRUE"
                    else:
                        params = ", ".join([f"x{i+1}" for i in range(arg_count)])
                        func_def = f"{op}({params}) == TRUE"
                    
                    # print(f"DEBUG: Iteration {iteration + 1}: Will add function: {func_def}")
                    functions_to_add.append(func_def)
                    iteration_added_funcs.append(op)
                    
                    # If this operator was previously added as a variable, mark it for removal
                    if op in added_variables:
                        variables_to_remove.append(op)
                        # print(f"DEBUG: Marking {op} for removal from VARIABLES (it's actually a function)")
                else:
                    # Add as constant
                    # print(f"DEBUG: {op} not used as function, treating as constant")
                    const_def = f"{op} == TRUE"
                    # print(f"DEBUG: Iteration {iteration + 1}: Will add constant: {const_def}")
                    functions_to_add.append(const_def)
                    iteration_added_funcs.append(op)

                    # If this operator was previously added as a variable, mark it for removal
                    if op in added_variables:
                        variables_to_remove.append(op)
                        print(f"DEBUG: Marking {op} for removal from VARIABLES (it's actually a constant)")
            
            # Add the functions to the file and remove incorrect variables if any were found
            if functions_to_add or variables_to_remove:
                # We need to know the action name to find its position
                # Extract action name from file path: ActionModule_ActionName.tla or task_ActionName.tla
                full_name = os.path.basename(file_path).replace("ActionModule_", "").replace(".tla", "")

                # Handle cases like "locksvc_Msg" -> "Msg" (when task name is prepended)
                action_name = full_name

                if task_name and full_name.startswith(f"{task_name}_"):
                    action_name = full_name[len(task_name)+1:]
                
                # Find insertion point - after EXTENDS but before the specific action definition
                insert_idx = 2  # Start from line 2 (skip MODULE and EXTENDS)
                
                # Find where VARIABLES declaration ends (if exists)
                for i, line in enumerate(lines):
                    if line.startswith("VARIABLES"):
                        insert_idx = i + 2  # After VARIABLES and empty line
                        break
                
                # Find where the specific action starts and insert BEFORE it
                print(f"DEBUG: Looking for action '{action_name}' starting from line 2")
                for i in range(2, len(lines)):  # Start from line 2
                    line = lines[i].strip()
                    print(f"DEBUG: Line {i}: '{line[:50]}...'")
                    # Look for the specific action definition by name
                    if line.startswith(f"{action_name}(") or line.startswith(f"{action_name} =="):
                        insert_idx = i  # Insert before the action definition
                        print(f"DEBUG: Found action '{action_name}' at line {i}: '{line[:50]}...', insert_idx = {insert_idx}")
                        break
                else:
                    print(f"DEBUG: Action '{action_name}' not found, using default position {insert_idx}")
                
                # Remove variables that are actually functions from VARIABLES declaration
                if variables_to_remove:
                    print(f"DEBUG: Removing variables that are actually functions: {variables_to_remove}")
                    for i, line in enumerate(lines):
                        if line.startswith("VARIABLES"):
                            # Parse existing variables
                            existing_vars = line.replace("VARIABLES", "").strip()
                            if existing_vars:
                                var_list = [v.strip() for v in existing_vars.split(",")]
                                # Remove variables that are actually functions
                                filtered_vars = [v for v in var_list if v and v not in variables_to_remove]
                                if filtered_vars:
                                    lines[i] = f"VARIABLES {', '.join(filtered_vars)}"
                                else:
                                    # Remove the entire VARIABLES line if no variables left
                                    lines[i] = ""
                                # print(f"DEBUG: Updated VARIABLES line: {lines[i]}")
                            break
                
                print(f"DEBUG: Will insert {len(functions_to_add)} functions at position {insert_idx}")
                print(f"DEBUG: Functions to add: {functions_to_add}")

                # Insert function definitions
                for i, func_def in enumerate(functions_to_add):
                    actual_insert_pos = insert_idx + i * 2
                    print(f"DEBUG: Inserting '{func_def}' at position {actual_insert_pos}")
                    lines.insert(actual_insert_pos, func_def)
                    lines.insert(actual_insert_pos + 1, "")  # Add empty line after each function
                
                # Write back to file
                updated_content = '\n'.join(lines)
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(updated_content)
                
                logger.debug(f"Iteration {iteration + 1}: Added {len(functions_to_add)} function definitions and removed {len(variables_to_remove)} incorrect variables")
            else:
                # print(f"DEBUG: Iteration {iteration + 1}: No new functions to add")
                pass

            # Always update all_added_funcs after each iteration, regardless of file changes
            all_added_funcs.extend(iteration_added_funcs)
            print(f"DEBUG: Updated all_added_funcs: {all_added_funcs}")

            # If no new functions were added in this iteration, we're done
            if not iteration_added_funcs:
                print(f"DEBUG: No new functions added in iteration {iteration + 1}, stopping")
                break
        
        # print(f"DEBUG: Completed iterative modification after {iteration + 1} iterations")
        # print(f"DEBUG: Total functions added across all iterations: {all_added_funcs}")
        return all_added_funcs
    
    def _aggregate_action_results(self, eval_result: SyntaxEvaluationResult, action_results: List[ActionValidationResult]):
        """
        Aggregate individual action results into the main evaluation result.
        
        Args:
            eval_result: Main evaluation result to update
            action_results: List of individual action validation results
        """
        if not action_results:
            return
        
        # Count successes and failures
        successful_actions = sum(1 for ar in action_results if ar.validation_result.success)
        total_actions = len(action_results)
        
        # Aggregate timing
        total_action_time = sum(ar.validation_result.compilation_time for ar in action_results)
        
        # Collect all errors
        all_syntax_errors = []
        all_semantic_errors = []
        for ar in action_results:
            all_syntax_errors.extend([f"{ar.action_name}: {error}" for error in ar.validation_result.syntax_errors])
            all_semantic_errors.extend([f"{ar.action_name}: {error}" for error in ar.validation_result.semantic_errors])
        
        # Update evaluation result with action-specific metrics
        eval_result.compilation_time += total_action_time
        eval_result.syntax_errors.extend(all_syntax_errors)
        eval_result.semantic_errors.extend(all_semantic_errors)
        
        # Add action decomposition specific metrics
        eval_result.total_actions = total_actions
        eval_result.successful_actions = successful_actions
        eval_result.action_success_rate = successful_actions / total_actions if total_actions > 0 else 0.0
        eval_result.action_results = action_results
        
        # Total variables and functions added during recovery
        eval_result.total_variables_added = sum(len(ar.variables_added) for ar in action_results)
        eval_result.total_functions_added = sum(len(ar.functions_added) for ar in action_results)
        eval_result.total_recovery_attempts = sum(ar.recovery_attempts for ar in action_results)
        
        logger.info(f"Action decomposition summary: {successful_actions}/{total_actions} actions successful ({eval_result.action_success_rate:.1%})")
    
    def _set_generation_result(self, eval_result: SyntaxEvaluationResult, generation_result: GenerationResult):
        """Set generation results on evaluation result"""
        eval_result.generation_successful = generation_result.success
        eval_result.generation_time = generation_result.metadata.get('latency_seconds', 0.0)
        eval_result.generated_specification = generation_result.generated_text
        
        if not generation_result.success:
            eval_result.generation_error = generation_result.error_message
    
    def _set_validation_result(self, eval_result: SyntaxEvaluationResult, validation_result: ValidationResult):
        """Set validation results on evaluation result"""
        eval_result.compilation_successful = validation_result.success
        eval_result.compilation_time += validation_result.compilation_time
        eval_result.syntax_errors.extend(validation_result.syntax_errors)
        eval_result.semantic_errors.extend(validation_result.semantic_errors)
        eval_result.compilation_output = validation_result.output
        
        # Legacy compatibility
        eval_result.compilation_errors = eval_result.syntax_errors + eval_result.semantic_errors
        
        # Overall success for action decomposition should only depend on individual action success
        # NOT on overall compilation success, since the whole point is to test actions separately
        eval_result.overall_success = (
            eval_result.generation_successful and 
            getattr(eval_result, 'action_success_rate', 0.0) > 0.0
        )
    
    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "syntax_action_decomposition"


# Convenience function for backward compatibility
def create_action_decomposition_evaluator(validation_timeout: int = 30, keep_temp_files: bool = False) -> ActionDecompositionEvaluator:
    """
    Factory function to create an action decomposition evaluator.
    
    Args:
        validation_timeout: Timeout for TLA+ validation in seconds
        keep_temp_files: Whether to keep temporary action files for debugging
        
    Returns:
        ActionDecompositionEvaluator instance
    """
    return ActionDecompositionEvaluator(validation_timeout=validation_timeout, keep_temp_files=keep_temp_files)