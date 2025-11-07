"""
Common result types for evaluation framework.
"""

import time
from typing import Dict, Any, List, Optional
from abc import ABC, abstractmethod


class EvaluationResult(ABC):
    """Base class for all evaluation results"""
    
    def __init__(self, task_name: str, method_name: str, model_name: str):
        self.task_name = task_name
        self.method_name = method_name
        self.model_name = model_name
        self.timestamp = time.time()
        self.overall_success = False
    
    @abstractmethod
    def to_dict(self) -> Dict[str, Any]:
        """Convert result to dictionary for serialization"""
        pass


class SyntaxEvaluationResult(EvaluationResult):
    """Result of syntax-level evaluation"""
    
    def __init__(self, task_name: str, method_name: str, model_name: str):
        super().__init__(task_name, method_name, model_name)
        
        # Generation results
        self.generation_successful = False
        self.generation_time = 0.0
        self.generation_error = None
        self.generated_specification = None
        
        # Compilation results
        self.compilation_successful = False
        self.compilation_time = 0.0
        self.syntax_errors = []
        self.semantic_errors = []
        self.compilation_output = ""
        
        # Action decomposition results (for action_decomposition metric)
        self.total_actions = 0
        self.successful_actions = 0
        self.action_success_rate = 0.0
        self.action_results = []  # List of ActionValidationResult objects
        self.total_variables_added = 0
        self.total_functions_added = 0
        self.total_recovery_attempts = 0
        
        # Legacy compatibility
        self.compilation_errors = []
    
    def to_dict(self) -> Dict[str, Any]:
        result = {
            "task_name": self.task_name,
            "method_name": self.method_name,
            "model_name": self.model_name,
            "timestamp": self.timestamp,
            "generation": {
                "successful": self.generation_successful,
                "time_seconds": self.generation_time,
                "error": self.generation_error,
                "specification_length": len(self.generated_specification) if self.generated_specification else 0
            },
            "compilation": {
                "successful": self.compilation_successful,
                "time_seconds": self.compilation_time,
                "syntax_errors": self.syntax_errors,
                "semantic_errors": self.semantic_errors,
                "syntax_error_count": len(self.syntax_errors),
                "semantic_error_count": len(self.semantic_errors),
                "total_error_count": len(self.compilation_errors),
                "output_length": len(self.compilation_output)
            },
            "overall": {
                "successful": self.overall_success,
                "total_time_seconds": self.generation_time + self.compilation_time
            }
        }
        
        # Add action decomposition metrics if available
        if self.total_actions > 0:
            result["action_decomposition"] = {
                "total_actions": self.total_actions,
                "successful_actions": self.successful_actions,
                "action_success_rate": self.action_success_rate,
                "variables_added": self.total_variables_added,
                "functions_added": self.total_functions_added,
                "recovery_attempts": self.total_recovery_attempts,
                "individual_results": [
                    {
                        "action_name": ar.action_name,
                        "successful": ar.validation_result.success,
                        "syntax_errors": len(ar.validation_result.syntax_errors),
                        "semantic_errors": len(ar.validation_result.semantic_errors),
                        "variables_added": ar.variables_added,
                        "functions_added": ar.functions_added,
                        "recovery_attempts": ar.recovery_attempts
                    } for ar in self.action_results
                ]
            }
        
        return result


class SemanticEvaluationResult(EvaluationResult):
    """Result of semantic-level evaluation"""
    
    def __init__(self, task_name: str, method_name: str, model_name: str):
        super().__init__(task_name, method_name, model_name)
        
        # Generation results (for compatibility with syntax evaluation)
        self.generation_time = 0.0
        
        # Invariant generation
        self.invariant_generation_successful = False
        self.invariant_generation_time = 0.0
        self.invariant_generation_error = None
        self.generated_invariants = []
        
        # Config generation
        self.config_generation_successful = False
        self.config_generation_time = 0.0
        self.config_generation_error = None
        self.config_file_path = None
        
        # Model checking
        self.model_checking_successful = False
        self.model_checking_time = 0.0
        self.model_checking_error = None
        self.states_explored = 0
        self.invariant_violations = []
        self.deadlock_found = False
        
        # File paths
        self.specification_file = None
        
        # Custom data for additional information
        self.custom_data = {}
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "task_name": self.task_name,
            "method_name": self.method_name,
            "model_name": self.model_name,
            "timestamp": self.timestamp,
            "generation_time": self.generation_time,
            "invariant_generation": {
                "successful": self.invariant_generation_successful,
                "time_seconds": self.invariant_generation_time,
                "error": self.invariant_generation_error,
                "invariants_count": len(self.generated_invariants)
            },
            "config_generation": {
                "successful": self.config_generation_successful,
                "time_seconds": self.config_generation_time,
                "error": self.config_generation_error,
                "config_file": self.config_file_path
            },
            "model_checking": {
                "successful": self.model_checking_successful,
                "time_seconds": self.model_checking_time,
                "error": self.model_checking_error,
                "states_explored": self.states_explored,
                "invariant_violations": self.invariant_violations,
                "deadlock_found": self.deadlock_found
            },
            "overall": {
                "successful": self.overall_success,
                "total_time_seconds": (self.invariant_generation_time + 
                                     self.config_generation_time + 
                                     self.model_checking_time)
            },
            "files": {
                "specification": self.specification_file,
                "config": self.config_file_path
            },
            "custom_data": self.custom_data
        }


class ConsistencyEvaluationResult(EvaluationResult):
    """Result of system consistency evaluation"""
    
    def __init__(self, task_name: str, method_name: str, model_name: str):
        super().__init__(task_name, method_name, model_name)
        
        # Trace generation
        self.trace_generation_successful = False
        self.trace_generation_time = 0.0
        self.trace_generation_error = None
        self.generated_trace_count = 0
        
        # Trace conversion
        self.trace_conversion_successful = False
        self.trace_conversion_time = 0.0
        self.trace_conversion_error = None
        
        # Trace validation
        self.trace_validation_successful = False
        self.trace_validation_time = 0.0
        self.trace_validation_error = None
        self.validated_events = 0
        
        # File paths
        self.raw_trace_files = []
        self.converted_trace_files = []
        self.specification_files = []
    
    def to_dict(self) -> Dict[str, Any]:
        return {
            "task_name": self.task_name,
            "method_name": self.method_name,
            "model_name": self.model_name,
            "timestamp": self.timestamp,
            "trace_generation": {
                "successful": self.trace_generation_successful,
                "time_seconds": self.trace_generation_time,
                "error": self.trace_generation_error,
                "trace_count": self.generated_trace_count
            },
            "trace_conversion": {
                "successful": self.trace_conversion_successful,
                "time_seconds": self.trace_conversion_time,
                "error": self.trace_conversion_error
            },
            "trace_validation": {
                "successful": self.trace_validation_successful,
                "time_seconds": self.trace_validation_time,
                "error": self.trace_validation_error,
                "validated_events": self.validated_events
            },
            "overall": {
                "successful": self.overall_success,
                "total_time_seconds": (self.trace_generation_time + 
                                     self.trace_conversion_time + 
                                     self.trace_validation_time)
            },
            "files": {
                "raw_traces": self.raw_trace_files,
                "converted_traces": self.converted_trace_files,
                "specifications": self.specification_files
            }
        }


class CompositeEvaluationResult(EvaluationResult):
    """Result of composite evaluation combining multiple metrics"""
    
    def __init__(self, task_name: str, method_name: str, model_name: str):
        super().__init__(task_name, method_name, model_name)
        
        # Generation results (shared across all evaluations)
        self.generation_successful = False
        self.generation_time = 0.0
        self.generation_error = None
        self.generated_specification = None
        
        # Sub-evaluation results
        self.action_decomposition_result: Optional[SyntaxEvaluationResult] = None
        self.compilation_check_result: Optional[SyntaxEvaluationResult] = None
        self.runtime_check_results: List[SemanticEvaluationResult] = []
        self.manual_invariant_result: Optional[SemanticEvaluationResult] = None
        self.coverage_result: Optional[SemanticEvaluationResult] = None
        
        # Global correction tracking
        self.total_corrections_attempted = 0
        self.successful_corrections = 0
        
    def to_dict(self) -> Dict[str, Any]:
        result = {
            "task_name": self.task_name,
            "method_name": self.method_name,
            "model_name": self.model_name,
            "timestamp": self.timestamp,
            "generation": {
                "successful": self.generation_successful,
                "time_seconds": self.generation_time,
                "error": self.generation_error,
                "specification_length": len(self.generated_specification) if self.generated_specification else 0
            },
            "overall": {
                "successful": self.overall_success,
                "total_time_seconds": self._calculate_total_time()
            }
        }
        
        # Add action decomposition results
        if self.action_decomposition_result:
            result["action_decomposition"] = self.action_decomposition_result.to_dict()
        
        # Add compilation check results
        if self.compilation_check_result:
            result["compilation_check"] = self.compilation_check_result.to_dict()
        
        # Add runtime check results
        if self.runtime_check_results:
            result["runtime_check"] = {
                "total_iterations": len(self.runtime_check_results),
                "successful_iterations": sum(1 for r in self.runtime_check_results if r.overall_success),
                "iterations": [r.to_dict() for r in self.runtime_check_results]
            }
        
        # Add manual invariant results
        if self.manual_invariant_result:
            result["manual_invariant"] = self.manual_invariant_result.to_dict()
        
        # Add coverage results
        if self.coverage_result:
            result["coverage"] = self.coverage_result.to_dict()
        
        return result
    
    def _calculate_total_time(self) -> float:
        """Calculate total evaluation time across all sub-evaluations"""
        total = self.generation_time
        
        if self.action_decomposition_result:
            total += self.action_decomposition_result.compilation_time
        
        if self.compilation_check_result:
            total += self.compilation_check_result.compilation_time
        
        for inv_result in self.runtime_check_results:
            total += (inv_result.invariant_generation_time + 
                     inv_result.config_generation_time + 
                     inv_result.model_checking_time)
        
        if self.manual_invariant_result:
            total += (self.manual_invariant_result.invariant_generation_time + 
                     self.manual_invariant_result.config_generation_time + 
                     self.manual_invariant_result.model_checking_time)
        
        return total