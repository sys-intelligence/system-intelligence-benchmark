"""
Base evaluator class for the evaluation framework.
"""

import json
import time
import logging
from pathlib import Path
from typing import List, Dict, Any, Optional
from abc import ABC, abstractmethod

from .result_types import EvaluationResult

logger = logging.getLogger(__name__)


class BaseEvaluator(ABC):
    """Base class for all evaluators in the framework"""
    
    def __init__(self, timeout: int = 30):
        """
        Initialize base evaluator.
        
        Args:
            timeout: Timeout for evaluation operations in seconds
        """
        self.timeout = timeout
        logger.info(f"{self.__class__.__name__} initialized with {timeout}s timeout")
    
    @abstractmethod
    def evaluate(self, *args, **kwargs) -> EvaluationResult:
        """Perform evaluation and return result"""
        pass
    
    def save_results(self, 
                    results: List[EvaluationResult], 
                    output_file: str,
                    include_specifications: bool = False):
        """
        Save evaluation results to JSON file.
        
        Args:
            results: List of evaluation results
            output_file: Output file path
            include_specifications: Whether to include generated specifications in output
        """
        logger.info(f"Saving {len(results)} results to {output_file}")
        
        # Convert results to dictionaries
        data = []
        for result in results:
            result_dict = result.to_dict()
            
            # Optionally include the generated specification
            if include_specifications and hasattr(result, 'generated_specification') and result.generated_specification:
                result_dict["generated_specification"] = result.generated_specification
            
            data.append(result_dict)
        
        # Add summary statistics
        summary = self._calculate_summary(results)
        
        output_data = {
            "evaluation_type": self._get_evaluation_type(),
            "total_evaluations": len(results),
            "timestamp": time.time(),
            "summary": summary,
            "results": data
        }
        
        # Save to file
        output_path = Path(output_file)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(output_data, f, indent=2, ensure_ascii=False)
        
        logger.info(f"Results saved to {output_path}")
    
    def _calculate_summary(self, results: List[EvaluationResult]) -> Dict[str, Any]:
        """Calculate summary statistics from evaluation results"""
        if not results:
            return {}
        
        total = len(results)
        overall_success = sum(1 for r in results if r.overall_success)
        
        summary = {
            "total_evaluations": total,
            "success_rates": {
                "overall": overall_success / total if total > 0 else 0.0
            },
            "counts": {
                "overall_successful": overall_success
            }
        }
        
        return summary
    
    @abstractmethod
    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        pass