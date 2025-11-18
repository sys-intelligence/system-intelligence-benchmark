"""
Composite Evaluator: Integrated evaluation combining multiple metrics.

This evaluator implements a comprehensive evaluation pipeline that:
1. Generates TLA+ specification once using agent-based method
2. Performs action decomposition evaluation
3. Performs compilation check evaluation 
4. If compilation succeeds, performs runtime check (3 iterations)
5. Aggregates all results into a unified composite result
"""

import logging
import time
from typing import Optional

from ...models.base import GenerationResult
from ...utils.output_manager import get_output_manager
from ..base.evaluator import BaseEvaluator
from ..base.result_types import CompositeEvaluationResult
from ..syntax.action_decomposition import ActionDecompositionEvaluator
from ..syntax.compilation_check import CompilationCheckEvaluator
from ..semantics.runtime_check import RuntimeCheckEvaluator
from ..semantics.manual_invariant_evaluator import ManualInvariantEvaluator
from ..semantics.coverage_evaluator import CoverageEvaluator
from ...core.verification.error_statistics_manager import get_error_statistics_manager

logger = logging.getLogger(__name__)


class CompositeEvaluator(BaseEvaluator):
    """
    Composite evaluator that runs multiple evaluation metrics in sequence.
    
    This evaluator provides a comprehensive evaluation by combining:
    - Action decomposition (syntax)
    - Compilation check (syntax) 
    - Invariant verification (semantics, conditional on compilation success)
    """
    
    def __init__(self,
                 validation_timeout: int = 90,
                 invariant_iterations: int = 3,
                 keep_temp_files: bool = False,
                 max_correction_attempts: int = 3,
                 enable_coverage: bool = True,
                 spec_language: str = "tla"):
        """
        Initialize composite evaluator.

        Args:
            validation_timeout: Timeout for validation in seconds
            invariant_iterations: Number of invariant verification iterations
            keep_temp_files: Whether to keep temporary files for debugging
            max_correction_attempts: Maximum number of global correction attempts
            enable_coverage: Whether to run coverage analysis
            spec_language: Target specification language ("tla", "alloy", "pat")
        """
        super().__init__(timeout=validation_timeout)
        self.max_iterations = invariant_iterations
        self.keep_temp_files = keep_temp_files
        self.max_correction_attempts = max_correction_attempts
        self.enable_coverage = enable_coverage
        self.spec_language = spec_language.lower().replace("+", "").strip()

        # Initialize language-specific evaluators
        self._init_evaluators(validation_timeout)

    def _init_evaluators(self, validation_timeout: int):
        """
        Initialize evaluators based on specification language.

        For TLA+: ActionDecomposition, Compilation, Runtime, ManualInvariant, Coverage
        For Alloy: Compilation, Runtime, ManualInvariant, Coverage (no action decomposition)

        Args:
            validation_timeout: Timeout for validation in seconds
        """
        if self.spec_language == "tla":
            # TLA+ evaluators
            self.action_evaluator = ActionDecompositionEvaluator(
                validation_timeout=validation_timeout,
                keep_temp_files=self.keep_temp_files
            )
            self.compilation_evaluator = CompilationCheckEvaluator(
                validation_timeout=validation_timeout
            )
            self.runtime_check_evaluator = RuntimeCheckEvaluator(
                tlc_timeout=validation_timeout
            )
            self.manual_invariant_evaluator = ManualInvariantEvaluator(
                tlc_timeout=validation_timeout
            )
            self.coverage_evaluator = CoverageEvaluator(
                tlc_timeout=validation_timeout
            )

        elif self.spec_language == "alloy":
            # Alloy evaluators - no action decomposition
            from ..syntax.alloy_compilation_check import AlloyCompilationCheckEvaluator
            from ..semantics.alloy_runtime_check import AlloyRuntimeCheckEvaluator
            from ..semantics.alloy_invariant_check import AlloyInvariantCheckEvaluator
            from ..semantics.alloy_coverage import AlloyCoverageEvaluator

            self.action_evaluator = None  # Alloy doesn't have action decomposition
            self.compilation_evaluator = AlloyCompilationCheckEvaluator(
                validation_timeout=validation_timeout
            )
            self.runtime_check_evaluator = AlloyRuntimeCheckEvaluator(
                validation_timeout=validation_timeout
            )
            self.manual_invariant_evaluator = AlloyInvariantCheckEvaluator(
                validation_timeout=validation_timeout
            )
            self.coverage_evaluator = AlloyCoverageEvaluator(
                validation_timeout=validation_timeout
            )

        else:
            raise ValueError(
                f"Unsupported specification language: '{self.spec_language}'. "
                f"Supported: tla, alloy"
            )
    
    def evaluate(self, 
                generation_result: GenerationResult,
                task_name: str,
                method_name: str,
                model_name: str,
                spec_module: str = None,
                task=None,
                method=None) -> CompositeEvaluationResult:
        """
        Perform comprehensive evaluation using 3-iteration approach.
        
        Workflow:
        - Up to 3 complete iterations, each containing:
          1. Action Decomposition
          2. Compilation Check  
          3. Runtime Check
        - If any iteration succeeds (all 3 phases pass), run Manual Invariant Verification
        - If iteration fails, collect errors and generate correction for next iteration
        
        Args:
            generation_result: Initial TLA+ specification generation result
            task_name: Name of the task being evaluated
            method_name: Name of the generation method
            model_name: Name of the language model
            spec_module: Optional specification module name
            task: Task object for corrections (required for correction functionality)
            method: Method object for corrections (required for correction functionality)
            
        Returns:
            CompositeEvaluationResult: Comprehensive evaluation results
        """
        logger.info(f"Starting composite evaluation: {task_name}/{method_name}/{model_name}")
        logger.info(f"Process: Up to {self.max_iterations} iterations of [Action Decomposition → Compilation Check → Runtime Check]")
        start_time = time.time()
        
        # Create composite result
        composite_result = CompositeEvaluationResult(task_name, method_name, model_name)
        
        # Use the provided generation result as starting point
        if not generation_result.success:
            logger.warning(f"Initial generation failed, cannot proceed with composite evaluation: {generation_result.error_message}")
            composite_result.overall_success = False
            composite_result.generation_error = generation_result.error_message
            return composite_result
        
        # Set initial generation results
        composite_result.generation_successful = generation_result.success
        composite_result.generation_time = generation_result.metadata.get('latency_seconds', 0.0)
        composite_result.generated_specification = generation_result.generated_text
        
        # Current working specification (will be iteratively improved)
        current_spec = generation_result.generated_text
        current_generation_result = generation_result
        
        # Track results for each iteration
        iteration_results = []
        successful_iteration = None
        
        try:
            # Run up to max_iterations complete evaluations
            for iteration in range(1, self.max_iterations + 1):
                logger.info(f"=== Iteration {iteration}/{self.max_iterations} ===")
                
                iteration_data = {
                    'iteration': iteration,
                    'action_result': None,
                    'compilation_result': None,
                    'runtime_result': None,
                    'success': False,
                    'errors': []
                }
                
                # Phase 1: Action Decomposition (TLA+ only, Alloy doesn't have this phase)
                if self.action_evaluator is not None:
                    logger.info(f"Iteration {iteration} - Phase 1/3: Action Decomposition")
                    try:
                        action_result = self.action_evaluator.evaluate(
                            current_generation_result, task_name, method_name, model_name, spec_module
                        )
                        iteration_data['action_result'] = action_result

                        success_rate = getattr(action_result, 'action_success_rate', 0.0) * 100
                        success_status = "✓ PASS" if action_result.overall_success else "✗ FAIL"
                        logger.info(f"  Action Decomposition: {success_status} ({success_rate:.1f}% actions successful)")

                        if not action_result.overall_success:
                            iteration_data['errors'].append(f"Action decomposition failed: {getattr(action_result, 'generation_error', 'Unknown error')}")

                    except Exception as e:
                        logger.error(f"  Action Decomposition failed with exception: {e}")
                        from ..base.result_types import SyntaxEvaluationResult
                        action_result = SyntaxEvaluationResult(task_name, method_name, model_name)
                        action_result.overall_success = False
                        action_result.generation_error = str(e)
                        iteration_data['action_result'] = action_result
                        iteration_data['errors'].append(f"Action decomposition exception: {str(e)}")
                else:
                    # Alloy: Skip action decomposition, create success result
                    logger.info(f"Iteration {iteration} - Phase 1/3: Action Decomposition (SKIPPED for {self.spec_language.upper()})")
                    from ..base.result_types import SyntaxEvaluationResult
                    action_result = SyntaxEvaluationResult(task_name, method_name, model_name)
                    action_result.overall_success = True  # Auto-pass for languages without action decomposition
                    iteration_data['action_result'] = action_result
                
                # Phase 2: Compilation Check
                logger.info(f"Iteration {iteration} - Phase 2/3: Compilation Check")
                logger.info(f"🔍 DEBUG: About to call compilation_evaluator.evaluate() - iteration {iteration}")
                try:
                    compilation_result = self.compilation_evaluator.evaluate(
                        current_generation_result, task_name, method_name, model_name, spec_module
                    )
                    logger.info(f"🔍 DEBUG: compilation_evaluator.evaluate() completed - iteration {iteration}, success={compilation_result.overall_success}")
                    iteration_data['compilation_result'] = compilation_result
                    
                    success_status = "✓ PASS" if compilation_result.overall_success else "✗ FAIL"
                    logger.info(f"  Compilation Check: {success_status}")
                    
                    if not compilation_result.overall_success:
                        errors = compilation_result.syntax_errors + compilation_result.semantic_errors
                        iteration_data['errors'].extend([f"Compilation error: {err}" for err in errors])
                        
                except Exception as e:
                    logger.error(f"  Compilation Check failed with exception: {e}")
                    from ..base.result_types import SyntaxEvaluationResult
                    compilation_result = SyntaxEvaluationResult(task_name, method_name, model_name)
                    compilation_result.overall_success = False
                    compilation_result.generation_error = str(e)
                    iteration_data['compilation_result'] = compilation_result
                    iteration_data['errors'].append(f"Compilation exception: {str(e)}")
                
                # Phase 3: Runtime Check (only if compilation passed)
                if compilation_result.overall_success:
                    logger.info(f"Iteration {iteration} - Phase 3/3: Runtime Check")
                    
                    # Ensure config file is available for runtime check
                    enhanced_generation_result, auto_config_file_path = self._ensure_config_file(
                        current_generation_result, task_name, method_name, model_name
                    )
                    
                    try:
                        runtime_result = self.runtime_check_evaluator.evaluate(
                            enhanced_generation_result, task_name, method_name, model_name, spec_module,
                            config_file_path=auto_config_file_path
                        )
                        iteration_data['runtime_result'] = runtime_result
                        
                        success_status = "✓ PASS" if runtime_result.overall_success else "✗ FAIL"
                        logger.info(f"  Runtime Check: {success_status}")
                        
                        if not runtime_result.overall_success:
                            error_msg = getattr(runtime_result, 'error_message', 'Runtime check failed')
                            iteration_data['errors'].append(f"Runtime error: {error_msg}")
                            
                    except Exception as e:
                        logger.error(f"  Runtime Check failed with exception: {e}")
                        from ..base.result_types import SemanticEvaluationResult
                        runtime_result = SemanticEvaluationResult(task_name, method_name, model_name)
                        runtime_result.overall_success = False
                        runtime_result.generation_error = str(e)
                        iteration_data['runtime_result'] = runtime_result
                        iteration_data['errors'].append(f"Runtime exception: {str(e)}")
                else:
                    logger.info(f"Iteration {iteration} - Phase 3/3: Runtime Check (SKIPPED - compilation failed)")
                    runtime_result = None
                    iteration_data['runtime_result'] = None
                
                # Check if this iteration succeeded
                iteration_success = (
                    action_result.overall_success and 
                    compilation_result.overall_success and 
                    runtime_result is not None and 
                    runtime_result.overall_success
                )
                
                iteration_data['success'] = iteration_success
                iteration_results.append(iteration_data)
                
                # Log iteration summary
                if iteration_success:
                    logger.info(f"Iteration {iteration}: ✓ SUCCESS (all phases passed)")
                    successful_iteration = iteration
                    
                    # Store the successful results
                    composite_result.action_decomposition_result = action_result
                    composite_result.compilation_check_result = compilation_result
                    composite_result.runtime_check_result = runtime_result
                    break
                else:
                    failed_phases = []
                    if not action_result.overall_success:
                        failed_phases.append("Action")
                    if not compilation_result.overall_success:
                        failed_phases.append("Compilation")
                    if runtime_result is None:
                        failed_phases.append("Runtime(SKIPPED)")
                    elif not runtime_result.overall_success:
                        failed_phases.append("Runtime")
                    
                    logger.info(f"Iteration {iteration}: ✗ FAILED ({', '.join(failed_phases)} failed)")
                    
                    # Store the latest results (even if failed)
                    composite_result.action_decomposition_result = action_result
                    composite_result.compilation_check_result = compilation_result
                    if runtime_result is not None:
                        composite_result.runtime_check_result = runtime_result
                    
                    # If not the last iteration, attempt correction
                    if iteration < self.max_iterations:
                        if task is not None and method is not None and hasattr(method, '_generate_correction'):
                            logger.info(f"Generating correction for iteration {iteration + 1}...")
                            all_errors = iteration_data['errors']
                            logger.info(f"Errors to fix: {len(all_errors)}")
                            
                            try:
                                # Get the model for correction
                                from ...config import get_configured_model
                                model_obj = get_configured_model(model_name)
                                
                                # Use agent_based's correction method
                                correction_result = method._generate_correction(task, current_spec, all_errors, model_obj)
                                
                                if correction_result.success:
                                    current_spec = correction_result.generated_text
                                    current_generation_result = GenerationResult(
                                        generated_text=current_spec,
                                        metadata=correction_result.metadata,
                                        timestamp=time.time(),
                                        success=True
                                    )
                                    logger.info(f"✓ Specification corrected for iteration {iteration + 1}")
                                    logger.info(f"🔍 DEBUG: Will use corrected spec for next iteration (length: {len(current_spec)} chars)")
                                else:
                                    logger.warning(f"✗ Correction failed, using original spec for iteration {iteration + 1}")
                                    logger.info(f"🔍 DEBUG: Will reuse original spec for next iteration (length: {len(current_spec)} chars)")
                                    
                            except Exception as e:
                                logger.error(f"Correction attempt failed: {e}")
                        else:
                            logger.warning(f"Cannot perform corrections - missing task/method objects or correction capability")
            
            # Step 4: Manual Invariant Verification (only if we had a successful iteration)
            if successful_iteration is not None:
                logger.info(f"Running Manual Invariant Verification (iteration {successful_iteration} succeeded)")
                
                # Try to reuse base config from the SUCCESSFUL runtime check to avoid redundant generation
                base_config_content = None
                if iteration_results and successful_iteration is not None:
                    runtime_result = None
                    # Find the runtime result from the successful iteration
                    for iter_result in iteration_results:
                        if iter_result.get('iteration') == successful_iteration and iter_result.get('runtime_result') and iter_result['runtime_result'].overall_success:
                            runtime_result = iter_result['runtime_result']
                            break
                    
                    if runtime_result and hasattr(runtime_result, 'config_file_path'):
                        config_file_path = runtime_result.config_file_path
                        try:
                            with open(config_file_path, 'r', encoding='utf-8') as f:
                                base_config_content = f.read()
                            logger.info("✓ Loaded base config from runtime check for manual invariant verification")
                        except Exception as e:
                            logger.warning(f"Failed to load config from runtime check: {e}")
                            base_config_content = None
                
                try:
                    # Try to get spec and config file paths from the SUCCESSFUL runtime check result
                    spec_file_path = None
                    config_file_path = None
                    
                    if iteration_results and successful_iteration is not None:
                        runtime_result = None
                        # Find the runtime result from the successful iteration
                        for iter_result in iteration_results:
                            if iter_result.get('iteration') == successful_iteration and iter_result.get('runtime_result') and iter_result['runtime_result'].overall_success:
                                runtime_result = iter_result['runtime_result']
                                break
                        
                        if runtime_result:
                            if hasattr(runtime_result, 'specification_file'):
                                spec_file_path = runtime_result.specification_file
                            if hasattr(runtime_result, 'config_file_path'):
                                config_file_path = runtime_result.config_file_path
                    
                    # Call manual invariant evaluator with composite mode parameters
                    manual_result = self.manual_invariant_evaluator.evaluate(
                        current_generation_result, task_name, method_name, model_name, spec_module, 
                        base_config_content, spec_file_path, config_file_path
                    )
                    
                    success_status = "✓ PASS" if manual_result.overall_success else "✗ FAIL"
                    logger.info(f"Manual Invariant Verification: {success_status}")
                    
                    composite_result.manual_invariant_result = manual_result
                    
                except Exception as e:
                    logger.error(f"Manual invariant verification failed: {e}")
                    from ..base.result_types import SemanticEvaluationResult
                    manual_result = SemanticEvaluationResult(task_name, method_name, model_name)
                    manual_result.overall_success = False
                    manual_result.generation_error = str(e)
                    composite_result.manual_invariant_result = manual_result
            else:
                logger.info(f"Skipping Manual Invariant Verification (no successful iteration)")
            
            # Step 5: Coverage Analysis (optional, run regardless of success status)
            if self.enable_coverage:
                logger.info("Running Coverage Analysis")
                
                try:
                    # Try to reuse files from the SUCCESSFUL runtime check if available
                    spec_file_path = None
                    config_file_path = None
                    
                    # Look for runtime check result with files from the successful iteration
                    if successful_iteration is not None and iteration_results:
                        runtime_result = None
                        # Find the runtime result from the successful iteration
                        for iter_result in iteration_results:
                            if iter_result.get('iteration') == successful_iteration and iter_result.get('runtime_result') and iter_result['runtime_result'].overall_success:
                                runtime_result = iter_result['runtime_result']
                                break
                        
                        if runtime_result and hasattr(runtime_result, 'specification_file'):
                            spec_file_path = runtime_result.specification_file
                            
                        if runtime_result and hasattr(runtime_result, 'config_file_path'):
                            config_file_path = runtime_result.config_file_path
                    
                    # Run coverage evaluation
                    coverage_result = self.coverage_evaluator.evaluate(
                        current_generation_result, task_name, method_name, model_name, spec_module,
                        spec_file_path=spec_file_path,
                        config_file_path=config_file_path
                    )
                    
                    success_status = "✓ PASS" if coverage_result.overall_success else "✗ FAIL"
                    logger.info(f"Coverage Analysis: {success_status}")
                    
                    composite_result.coverage_result = coverage_result
                    
                except Exception as e:
                    logger.error(f"Coverage analysis failed: {e}")
                    from ..base.result_types import SemanticEvaluationResult
                    coverage_result = SemanticEvaluationResult(task_name, method_name, model_name)
                    coverage_result.overall_success = False
                    coverage_result.model_checking_error = str(e)
                    composite_result.coverage_result = coverage_result
            else:
                logger.info("Coverage Analysis disabled")
            
            # Determine overall success
            composite_result.overall_success = successful_iteration is not None
            
            # Log final summary
            logger.info(f"Composite evaluation summary: {len(iteration_results)} iterations, {'success' if successful_iteration else 'failure'}")
            
            # Create output directory and save results
            output_manager = get_output_manager()
            output_dir = output_manager.create_experiment_dir("composite", task_name, method_name, model_name)
            
            # Print evaluation summary
            self._print_evaluation_summary_new(
                iteration_results, successful_iteration, composite_result, output_dir
            )
            
            # Save composite result
            composite_result.output_directory = output_dir
            
            # Prepare result data and metadata for saving
            def _serialize_result(result_obj):
                """Convert evaluation result objects into JSON-serializable data."""
                if result_obj is None:
                    return None
                if hasattr(result_obj, 'to_dict'):
                    return result_obj.to_dict()
                return result_obj

            result_data = {
                'overall_success': composite_result.overall_success,
                'generation_time': composite_result.generation_time,
                'action_decomposition': _serialize_result(getattr(composite_result, 'action_decomposition_result', None)),
                'compilation_check': _serialize_result(getattr(composite_result, 'compilation_check_result', None)),
                'runtime_check': _serialize_result(getattr(composite_result, 'runtime_check_result', None)),
                'manual_invariant': _serialize_result(getattr(composite_result, 'manual_invariant_result', None))
            }
            
            metadata = {
                'task_name': task_name,
                'method_name': method_name,
                'model_name': model_name,
                'timestamp': time.time(),
                'successful_iteration': successful_iteration,
                'total_iterations': len(iteration_results)
            }
            
            output_manager.save_result(output_dir, result_data, metadata)
            logger.info(f"Composite results saved to: {output_dir}")
            
            # Save experiment error statistics to output directory
            try:
                stats_manager = get_error_statistics_manager()
                stats_file_path = stats_manager.save_experiment_statistics(
                    output_dir, task_name, method_name, model_name
                )
                logger.info(f"Experiment error statistics saved to: {stats_file_path}")
                
                # Reset experiment statistics for next run
                stats_manager.reset_experiment_statistics()
                
            except Exception as e:
                logger.warning(f"Failed to save experiment error statistics: {e}")
        
        finally:
            # Results already saved in try block
            pass
        
        end_time = time.time()
        total_time = end_time - start_time
        logger.info(f"Composite evaluation complete: success={composite_result.overall_success}, total_time={total_time:.2f}s")
        
        return composite_result
    
    def _print_evaluation_summary(self, action_results_history, compilation_success_round, invariant_success_round, global_correction_attempts, composite_result, output_dir=None):
        """Print detailed evaluation summary with results from all rounds."""
        # Generate experiment data for JSON export
        experiment_data = self._generate_experiment_data(
            action_results_history, compilation_success_round, invariant_success_round, 
            global_correction_attempts, composite_result
        )
        
        # Save experiment data as JSON
        if output_dir:
            self._save_experiment_data(experiment_data, output_dir)
        
        # Print improved summary
        self._print_improved_summary(experiment_data, action_results_history, 
                                   compilation_success_round, invariant_success_round,
                                   global_correction_attempts, composite_result)
    
    def _set_generation_result(self, composite_result: CompositeEvaluationResult, generation_result: GenerationResult):
        """Set generation results on composite result"""
        composite_result.generation_successful = generation_result.success
        composite_result.generation_time = generation_result.metadata.get('latency_seconds', 0.0)
        composite_result.generated_specification = generation_result.generated_text
        
        if not generation_result.success:
            composite_result.generation_error = generation_result.error_message
    
    def _calculate_overall_success(self, composite_result: CompositeEvaluationResult) -> bool:
        """
        Calculate overall success based on all sub-evaluation results.
        
        Success criteria:
        - Generation must succeed
        - At least one of action decomposition or compilation check must succeed
        - If invariant verification ran, at least one iteration must succeed
        """
        if not composite_result.generation_successful:
            return False
        
        # Check syntax evaluations
        action_success = (composite_result.action_decomposition_result and 
                         composite_result.action_decomposition_result.overall_success)
        compilation_success = (composite_result.compilation_check_result and 
                              composite_result.compilation_check_result.overall_success)
        
        syntax_success = action_success or compilation_success
        
        # Check invariant verification if it ran
        if composite_result.runtime_check_results:
            inv_success = any(r.overall_success for r in composite_result.runtime_check_results)
            
            # If manual invariant also ran, consider it in success calculation
            if composite_result.manual_invariant_result:
                manual_inv_success = composite_result.manual_invariant_result.overall_success
                return syntax_success and inv_success and manual_inv_success
            
            return syntax_success and inv_success
        
        return syntax_success
    
    def _save_composite_results(self, composite_result: CompositeEvaluationResult, output_dir):
        """Save composite evaluation results to output directory"""
        
        # Prepare comprehensive result data
        result_data = composite_result.to_dict()
        
        # Add summary statistics
        result_data["summary"] = {
            "generation_successful": composite_result.generation_successful,
            "action_decomposition_successful": (
                composite_result.action_decomposition_result.overall_success 
                if composite_result.action_decomposition_result else False
            ),
            "compilation_successful": (
                composite_result.compilation_check_result.overall_success 
                if composite_result.compilation_check_result else False
            ),
            "runtime_check_iterations": len(composite_result.runtime_check_results),
            "runtime_check_successful_iterations": sum(
                1 for r in composite_result.runtime_check_results if r.overall_success
            ),
            "overall_successful": composite_result.overall_success
        }
        
        metadata = {
            "task_name": composite_result.task_name,
            "method_name": composite_result.method_name,
            "model_name": composite_result.model_name,
            "metric": "composite",
            "evaluation_timestamp": time.time(),
            "validation_timeout": self.timeout,
            "invariant_iterations": self.invariant_iterations,
            "keep_temp_files": self.keep_temp_files
        }
        
        # Save specification to output directory
        if composite_result.generated_specification:
            spec_file_path = output_dir / f"{composite_result.task_name}.tla"
            with open(spec_file_path, 'w', encoding='utf-8') as f:
                f.write(composite_result.generated_specification)
            metadata["specification_file"] = str(spec_file_path)
        
        output_manager = get_output_manager()
        output_manager.save_result(output_dir, result_data, metadata)
        logger.info(f"Composite results saved to: {output_dir}")
        
        # Store output directory path in result for display
        composite_result.output_directory = str(output_dir)
    
    def _calculate_composite_generation_stats(self, composite_result: CompositeEvaluationResult):
        """Calculate overall generation statistics from composite evaluation process"""
        # Count total evaluations performed
        total_evaluations = 1  # Action decomposition
        total_evaluations += 1  # Compilation check
        if composite_result.runtime_check_results:
            total_evaluations += 1  # Invariant verification (if executed)
        
        # Count successful evaluations
        successful_evaluations = 0
        if composite_result.action_decomposition_result and composite_result.action_decomposition_result.overall_success:
            successful_evaluations += 1
        if composite_result.compilation_check_result and composite_result.compilation_check_result.overall_success:
            successful_evaluations += 1
        if composite_result.runtime_check_results:
            if any(r.overall_success for r in composite_result.runtime_check_results):
                successful_evaluations += 1
        
        logger.info(f"Composite evaluation summary: {successful_evaluations}/{total_evaluations} phases successful")
        logger.info(f"Initial generation time: {composite_result.generation_time:.2f}s")
        
        # The generated_specification contains the final (possibly corrected) version
    
    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "composite"
    
    def _create_output_directory(self, task_name: str, method_name: str, model_name: str):
        """Create output directory for composite evaluation results."""
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="composite",
            task=task_name,
            method=method_name, 
            model=model_name
        )
        return output_dir
    
    def _print_evaluation_summary_new(self, iteration_results, successful_iteration, composite_result, output_dir=None):
        """Print detailed evaluation summary with results from all iterations."""
        # Generate experiment data for JSON export
        experiment_data = self._generate_experiment_data_new(
            iteration_results, successful_iteration, composite_result
        )
        
        # Save experiment data as JSON
        if output_dir:
            import json
            json_file = f"{output_dir}/experiment_data.json"
            with open(json_file, 'w') as f:
                json.dump(experiment_data, f, indent=2)
            logger.info(f"Experiment data saved to: {json_file}")
        
        # Extract summary information
        summary = experiment_data['summary']
        
        # Print detailed summary with consistent formatting
        logger.info("=" * 70)
        logger.info("COMPOSITE EVALUATION SUMMARY")
        logger.info("=" * 70)
        
        overall_status = "✓ SUCCESS" if summary['overall_success'] else "✗ FAILURE"
        logger.info(f"📊 OVERALL RESULT: {overall_status}")
        logger.info(f"📈 Total Iterations: {summary['total_iterations']}")
        logger.info(f"⏱️  Generation Time: {summary['generation_time']:.1f}s")
        logger.info(f"⏱️  Total Time: {summary['total_evaluation_time']:.1f}s")
        logger.info("")
        
        # Iteration breakdown
        logger.info("🔄 ITERATION BREAKDOWN:")
        for iter_data in experiment_data['iterations']:
            iter_num = iter_data['iteration']
            action_status = "✓ PASS" if iter_data['phases']['action']['success'] else "✗ FAIL"
            compile_status = "✓ PASS" if iter_data['phases']['compilation']['success'] else "✗ FAIL"
            runtime_status = iter_data['phases']['runtime']['status']
            
            if runtime_status == "skipped":
                runtime_display = "⚠ SKIPPED"
            elif iter_data['phases']['runtime']['success']:
                runtime_display = "✓ PASS"
            else:
                runtime_display = "✗ FAIL"
            
            logger.info(f"  Iteration {iter_num}:")
            logger.info(f"    Phase 1 (Actions): {action_status} ({iter_data['phases']['action']['success_rate']:.1f}%)")
            logger.info(f"    Phase 2 (Compile): {compile_status}")
            logger.info(f"    Phase 3 (Runtime): {runtime_display}")
        
        logger.info("")
        
        # Final phase statistics
        logger.info("📈 FINAL PHASE STATISTICS:")
        if successful_iteration:
            final_iter = next(iter_data for iter_data in experiment_data['iterations'] if iter_data['iteration'] == successful_iteration)
            logger.info(f"  Phase 1 (Action Decomposition): ✓ ({final_iter['phases']['action']['success_rate']:.1f}%)")
            logger.info(f"  Phase 2 (Compilation Check): ✓")
            logger.info(f"  Phase 3 (Runtime Check): ✓")
            
            # Manual invariant results
            if hasattr(composite_result, 'manual_invariant_result') and composite_result.manual_invariant_result:
                manual_result = composite_result.manual_invariant_result
                manual_status = "✓" if manual_result.overall_success else "✗"
                logger.info(f"  Phase 4 (Manual Invariants): {manual_status}")
            else:
                logger.info(f"  Phase 4 (Manual Invariants): ⚠ NOT EXECUTED")
            
            # Coverage analysis results
            if hasattr(composite_result, 'coverage_result') and composite_result.coverage_result:
                coverage_result = composite_result.coverage_result
                coverage_status = "✓" if coverage_result.overall_success else "✗"
                logger.info(f"  Phase 5 (Coverage Analysis): {coverage_status}")
            else:
                logger.info(f"  Phase 5 (Coverage Analysis): ⚠ NOT EXECUTED")
        else:
            # Show results from the last iteration
            if iteration_results:
                last_iter = iteration_results[-1]
                action_status = "✓" if last_iter['action_result'] and last_iter['action_result'].overall_success else "✗"
                compile_status = "✓" if last_iter['compilation_result'] and last_iter['compilation_result'].overall_success else "✗"
                runtime_status = "✗" if last_iter['runtime_result'] and not last_iter['runtime_result'].overall_success else "⚠ NOT EXECUTED"
                
                logger.info(f"  Phase 1 (Action Decomposition): {action_status}")
                logger.info(f"  Phase 2 (Compilation Check): {compile_status}")
                logger.info(f"  Phase 3 (Runtime Check): {runtime_status}")
                logger.info(f"  Phase 4 (Manual Invariants): ⚠ NOT EXECUTED")
                
                # Coverage analysis results
                if hasattr(composite_result, 'coverage_result') and composite_result.coverage_result:
                    coverage_result = composite_result.coverage_result
                    coverage_status = "✓" if coverage_result.overall_success else "✗"
                    logger.info(f"  Phase 5 (Coverage Analysis): {coverage_status}")
                else:
                    logger.info(f"  Phase 5 (Coverage Analysis): ⚠ NOT EXECUTED")
        
        logger.info("=" * 70)
    
    def _generate_experiment_data_new(self, iteration_results, successful_iteration, composite_result):
        """Generate structured experiment data for JSON export with new format."""
        
        # Calculate iteration statistics
        total_iterations = len(iteration_results)
        
        # Phase results for each iteration
        iterations_data = []
        for iter_data in iteration_results:
            iteration_num = iter_data['iteration']
            
            # Action decomposition data
            action_result = iter_data['action_result']
            action_success = action_result.overall_success if action_result else False
            action_success_rate = getattr(action_result, 'action_success_rate', 0.0) * 100 if action_result else 0.0
            
            # Compilation data
            compile_result = iter_data['compilation_result']
            compile_success = compile_result.overall_success if compile_result else False
            
            # Runtime data
            runtime_result = iter_data['runtime_result']
            if runtime_result is None:
                runtime_status = "skipped"
                runtime_success = False
            else:
                runtime_status = "executed"
                runtime_success = runtime_result.overall_success
            
            iterations_data.append({
                'iteration': iteration_num,
                'success': iter_data['success'],
                'phases': {
                    'action': {
                        'success': action_success,
                        'success_rate': action_success_rate,
                        'total_actions': getattr(action_result, 'total_actions', 0) if action_result else 0,
                        'successful_actions': getattr(action_result, 'successful_actions', 0) if action_result else 0
                    },
                    'compilation': {
                        'success': compile_success
                    },
                    'runtime': {
                        'status': runtime_status,
                        'success': runtime_success
                    }
                },
                'errors': iter_data.get('errors', [])
            })
        
        # Manual invariant verification data
        manual_inv_data = {}
        if hasattr(composite_result, 'manual_invariant_result') and composite_result.manual_invariant_result:
            manual_result = composite_result.manual_invariant_result
            manual_inv_data = {
                'executed': True,
                'success': manual_result.overall_success,
                'total_invariants': manual_result.custom_data.get('total_invariants', 0) if hasattr(manual_result, 'custom_data') and manual_result.custom_data else 0,
                'passed_invariants': manual_result.custom_data.get('passed_invariants', 0) if hasattr(manual_result, 'custom_data') and manual_result.custom_data else 0,
                'failed_invariants': manual_result.custom_data.get('failed_invariants', []) if hasattr(manual_result, 'custom_data') and manual_result.custom_data else []
            }
        else:
            manual_inv_data = {
                'executed': False,
                'success': False,
                'total_invariants': 0,
                'passed_invariants': 0,
                'failed_invariants': []
            }
        
        return {
            'summary': {
                'overall_success': successful_iteration is not None,
                'successful_iteration': successful_iteration,
                'total_iterations': total_iterations,
                'generation_time': composite_result.generation_time,
                'total_evaluation_time': 0.0  # Will be filled by caller
            },
            'iterations': iterations_data,
            'manual_invariant_verification': manual_inv_data,
            'metadata': {
                'task': getattr(composite_result, 'task_name', ''),
                'method': getattr(composite_result, 'method_name', ''),
                'model': getattr(composite_result, 'model_name', ''),
                'timestamp': time.time()
            }
        }
    
    def _generate_experiment_data(self, action_results_history, compilation_success_round, 
                                invariant_success_round, global_correction_attempts, composite_result):
        """Generate structured experiment data for JSON export."""
        
        # Calculate iteration statistics - handle any number of iterations
        total_iterations = len(action_results_history)
        successful_iteration = None
        if compilation_success_round is not None and invariant_success_round is not None:
            successful_iteration = max(compilation_success_round, invariant_success_round) + 1
        
        # Phase results for each iteration
        phase_results = []
        phase4_passed = 0
        phase4_total = 0
        phase4_failed_invariants = []
        
        for i, action_result in enumerate(action_results_history):
            iteration = i + 1
            
            # Phase 1: Action Decomposition
            if 'error' in action_result:
                phase1_success = False
                phase1_ratio = 0.0
            else:
                phase1_success = action_result['success_rate'] >= 1.0
                phase1_ratio = action_result['success_rate']
            
            # Phase 2: Compilation Check 
            phase2_success = compilation_success_round is not None and compilation_success_round < iteration
            
            # Phase 3: Runtime Check
            phase3_success = invariant_success_round is not None and invariant_success_round < iteration
            
            # Phase 4: Manual Invariant Verification (only if phases 1-3 passed)
            phase4_success = False
            iter_phase4_passed = 0
            iter_phase4_total = 0
            iter_phase4_failed_invariants = []
            
            if phase1_success and phase2_success and phase3_success and composite_result.manual_invariant_result:
                phase4_success = composite_result.manual_invariant_result.overall_success
                if composite_result.manual_invariant_result.custom_data:
                    iter_phase4_passed = composite_result.manual_invariant_result.custom_data.get('passed_invariants', 0)
                    iter_phase4_total = composite_result.manual_invariant_result.custom_data.get('total_invariants', 0)
                    iter_phase4_failed_invariants = composite_result.manual_invariant_result.custom_data.get('failed_invariants', [])
                    
                    # Store for final statistics
                    phase4_passed = iter_phase4_passed
                    phase4_total = iter_phase4_total
                    phase4_failed_invariants = iter_phase4_failed_invariants
            
            phase_results.append({
                "iteration": iteration,
                "phase1_action_decomposition": {
                    "success": phase1_success,
                    "success_ratio": phase1_ratio
                },
                "phase2_compilation": {
                    "success": phase2_success
                },
                "phase3_runtime": {
                    "success": phase3_success
                },
                "phase4_manual_invariant": {
                    "success": phase4_success,
                    "passed_invariants": iter_phase4_passed,
                    "total_invariants": iter_phase4_total,
                    "failed_invariants": iter_phase4_failed_invariants
                }
            })
        
        # Get final phase success states
        final_phase1_success = phase_results[-1]["phase1_action_decomposition"]["success"] if phase_results else False
        final_phase1_ratio = phase_results[-1]["phase1_action_decomposition"]["success_ratio"] if phase_results else 0.0
        
        return {
            "summary": {
                "total_iterations": total_iterations,
                "successful_iteration": successful_iteration,
                "final_success": composite_result.overall_success,
                "generation_time_seconds": composite_result.generation_time,
                "total_evaluation_time_seconds": getattr(composite_result, 'total_time', 0.0)
            },
            "phase_statistics": {
                "phase1_action_decomposition": {
                    "final_success": final_phase1_success,
                    "final_success_ratio": final_phase1_ratio
                },
                "phase2_compilation": {
                    "success": compilation_success_round is not None
                },
                "phase3_runtime": {
                    "success": invariant_success_round is not None  
                },
                "phase4_manual_invariant": {
                    "success": composite_result.manual_invariant_result.overall_success if composite_result.manual_invariant_result else False,
                    "passed_invariants": phase4_passed,
                    "total_invariants": phase4_total,
                    "success_ratio": phase4_passed / phase4_total if phase4_total > 0 else 0.0,
                    "failed_invariants": phase4_failed_invariants
                }
            },
            "iteration_details": phase_results
        }

    def _save_experiment_data(self, experiment_data, output_dir):
        """Save experiment data as JSON for automated analysis."""
        import json
        from pathlib import Path
        
        if not output_dir:
            return
        
        output_path = Path(output_dir)
        json_file = output_path / "experiment_data.json"
        
        try:
            with open(json_file, 'w', encoding='utf-8') as f:
                json.dump(experiment_data, f, indent=2, ensure_ascii=False)
            logger.info(f"Experiment data saved to: {json_file}")
        except Exception as e:
            logger.warning(f"Failed to save experiment data: {e}")

    def _print_improved_summary(self, experiment_data, action_results_history, 
                              compilation_success_round, invariant_success_round,
                              global_correction_attempts, composite_result):
        """Print improved, clear summary of composite evaluation results."""
        
        logger.info("=" * 70)
        logger.info("COMPOSITE EVALUATION SUMMARY")
        logger.info("=" * 70)
        
        # Overall Results
        summary = experiment_data["summary"]
        logger.info(f"📊 OVERALL RESULT: {'✓ SUCCESS' if summary['final_success'] else '✗ FAILURE'}")
        logger.info(f"📈 Total Iterations: {summary['total_iterations']}")
        if summary['successful_iteration']:
            logger.info(f"🎯 Success achieved in: Iteration {summary['successful_iteration']}")
        logger.info(f"⏱️  Generation Time: {summary['generation_time_seconds']:.1f}s")
        logger.info(f"⏱️  Total Time: {summary['total_evaluation_time_seconds']:.1f}s")
        
        logger.info("")
        logger.info("🔄 ITERATION BREAKDOWN:")
        
        # Iteration Details - handle any number of iterations
        for iteration_data in experiment_data["iteration_details"]:
            iter_num = iteration_data["iteration"]
            logger.info(f"  Iteration {iter_num}:")
            
            # Phase 1
            p1 = iteration_data["phase1_action_decomposition"]
            status1 = "✓ PASS" if p1["success"] else "✗ FAIL"
            logger.info(f"    Phase 1 (Actions): {status1} ({p1['success_ratio']:.1%})")
            
            if p1["success"]:
                # Phase 2
                p2 = iteration_data["phase2_compilation"]  
                status2 = "✓ PASS" if p2["success"] else "✗ FAIL"
                logger.info(f"    Phase 2 (Compile): {status2}")
                
                if p2["success"]:
                    # Phase 3  
                    p3 = iteration_data["phase3_runtime"]
                    status3 = "✓ PASS" if p3["success"] else "✗ FAIL"
                    logger.info(f"    Phase 3 (Runtime): {status3}")
                    
                    if p3["success"]:
                        # Phase 4
                        p4 = iteration_data["phase4_manual_invariant"]
                        if p4["total_invariants"] > 0:
                            status4 = "✓ PASS" if p4["success"] else "✗ FAIL"
                            logger.info(f"    Phase 4 (Invariants): {status4} ({p4['passed_invariants']}/{p4['total_invariants']})")
                            if p4["failed_invariants"]:
                                logger.info(f"      Failed: {', '.join(p4['failed_invariants'])}")
                        else:
                            logger.info(f"    Phase 4 (Invariants): ⚠ SKIPPED")
                    else:
                        logger.info(f"    Phase 4 (Invariants): ⚠ SKIPPED (Phase 3 failed)")
                else:
                    logger.info(f"    Phase 3 (Runtime): ⚠ SKIPPED (Phase 2 failed)")
                    logger.info(f"    Phase 4 (Invariants): ⚠ SKIPPED (Phase 2 failed)")
            else:
                logger.info(f"    Phase 2 (Compile): ⚠ SKIPPED (Phase 1 failed)")
                logger.info(f"    Phase 3 (Runtime): ⚠ SKIPPED (Phase 1 failed)")  
                logger.info(f"    Phase 4 (Invariants): ⚠ SKIPPED (Phase 1 failed)")
        
        logger.info("")
        logger.info("📈 FINAL PHASE STATISTICS:")
        stats = experiment_data["phase_statistics"]
        logger.info(f"  Phase 1 (Action Decomposition): {'✓' if stats['phase1_action_decomposition']['final_success'] else '✗'} ({stats['phase1_action_decomposition']['final_success_ratio']:.1%})")
        logger.info(f"  Phase 2 (Compilation Check): {'✓' if stats['phase2_compilation']['success'] else '✗'}")
        logger.info(f"  Phase 3 (Runtime Check): {'✓' if stats['phase3_runtime']['success'] else '✗'}")
        
        p4_stats = stats['phase4_manual_invariant']
        if p4_stats['total_invariants'] > 0:
            logger.info(f"  Phase 4 (Manual Invariants): {'✓' if p4_stats['success'] else '✗'} ({p4_stats['passed_invariants']}/{p4_stats['total_invariants']}, {p4_stats['success_ratio']:.1%})")
            if p4_stats['failed_invariants']:
                logger.info(f"    Failed Invariants: {', '.join(p4_stats['failed_invariants'])}")
        else:
            logger.info(f"  Phase 4 (Manual Invariants): ⚠ NOT EXECUTED")
        
        logger.info("=" * 70)

    def _ensure_config_file(self, generation_result, task_name: str, method_name: str, model_name: str):
        """
        Ensure that a config file is available for runtime check.
        If no config file is provided in metadata, generate one automatically.
        
        Args:
            generation_result: The current GenerationResult
            task_name: Name of the task
            method_name: Name of the method
            model_name: Name of the model
            
        Returns:
            Tuple of (generation_result, config_file_path) where config_file_path is None if no config available
        """
        # Check if config file is already provided
        if (generation_result.metadata and 
            generation_result.metadata.get('config_file') and
            generation_result.metadata.get('config_file') != 'None'):
            config_file_path = generation_result.metadata['config_file']
            logger.info(f"Using existing config file: {config_file_path}")
            return generation_result, config_file_path
        
        # Generate config file automatically
        logger.info("No config file provided, generating one automatically...")
        
        try:
            # Import ConfigGenerator
            from ..semantics.runtime_check import ConfigGenerator
            config_generator = ConfigGenerator()
            
            # Get TLA+ content from generation result
            tla_content = generation_result.generated_text
            if not tla_content or not tla_content.strip():
                logger.warning("No TLA+ content available for config generation")
                return generation_result, None
            
            # Generate basic invariants from the spec (simple approach)
            invariants = self._extract_basic_invariants(tla_content)
            
            # Generate config file
            success, config_content, error = config_generator.generate_config(
                tla_content, invariants, task_name, model_name
            )
            
            if success and config_content:
                logger.info("✓ Config file generated successfully")
                
                # Create temporary config file
                import tempfile
                import os
                
                # Create temp file in same directory as other outputs for consistency  
                temp_dir = tempfile.gettempdir()
                config_file_fd, config_file_path = tempfile.mkstemp(
                    suffix='.cfg', 
                    prefix=f'{task_name}_{model_name}_auto_',
                    dir=temp_dir
                )
                
                # Write config content to file
                with os.fdopen(config_file_fd, 'w', encoding='utf-8') as f:
                    f.write(config_content)
                
                logger.info(f"Auto-generated config saved to: {config_file_path}")
                return generation_result, config_file_path
            else:
                logger.warning(f"Config generation failed: {error}")
                return generation_result, None
                
        except Exception as e:
            logger.warning(f"Failed to generate config file: {e}")
            return generation_result, None
    
    def _extract_basic_invariants(self, tla_content: str) -> str:
        """
        Extract basic invariants from TLA+ specification.
        This is a simple heuristic approach.
        
        Args:
            tla_content: The TLA+ specification content
            
        Returns:
            String containing basic invariants
        """
        # Simple approach: look for common invariant patterns
        invariants = []
        
        lines = tla_content.split('\n')
        for line in lines:
            line = line.strip()
            # Look for variable declarations
            if line.startswith('VARIABLES'):
                # Add type invariants for variables
                continue
            # Look for Init predicate
            elif 'Init ==' in line:
                invariants.append("TypeOK")
                invariants.append("Init")
                break
        
        # Add some common invariants
        if not invariants:
            invariants = ["TypeOK"]
        
        return "\n".join([f"INVARIANT {inv}" for inv in invariants])


# Convenience function for backward compatibility
def create_composite_evaluator(validation_timeout: int = 30,
                              invariant_iterations: int = 3,
                              keep_temp_files: bool = False,
                              spec_language: str = "tla") -> CompositeEvaluator:
    """
    Factory function to create a composite evaluator.

    Args:
        validation_timeout: Timeout for validation in seconds
        invariant_iterations: Number of invariant verification iterations
        keep_temp_files: Whether to keep temporary files for debugging
        spec_language: Target specification language ("tla", "alloy", "pat")

    Returns:
        CompositeEvaluator instance
    """
    return CompositeEvaluator(
        validation_timeout=validation_timeout,
        invariant_iterations=invariant_iterations,
        keep_temp_files=keep_temp_files,
        spec_language=spec_language
    )
