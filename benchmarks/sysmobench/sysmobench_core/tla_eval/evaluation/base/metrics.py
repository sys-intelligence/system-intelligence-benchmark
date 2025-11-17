"""
Common metrics and utilities for evaluation.
"""

import time
from typing import Dict, Any, List
from collections import defaultdict


class MetricsCollector:
    """Utility class for collecting and aggregating metrics"""
    
    def __init__(self):
        self.metrics = defaultdict(list)
        self.start_times = {}
    
    def start_timer(self, operation: str):
        """Start timing an operation"""
        self.start_times[operation] = time.time()
    
    def end_timer(self, operation: str) -> float:
        """End timing an operation and return elapsed time"""
        if operation not in self.start_times:
            return 0.0
        
        elapsed = time.time() - self.start_times[operation]
        self.metrics[f"{operation}_time"].append(elapsed)
        del self.start_times[operation]
        return elapsed
    
    def record_metric(self, name: str, value: Any):
        """Record a metric value"""
        self.metrics[name].append(value)
    
    def get_summary(self) -> Dict[str, Any]:
        """Get summary statistics for all recorded metrics"""
        summary = {}
        
        for metric_name, values in self.metrics.items():
            if not values:
                continue
                
            if isinstance(values[0], (int, float)):
                # Numeric metrics
                summary[metric_name] = {
                    "count": len(values),
                    "total": sum(values),
                    "average": sum(values) / len(values),
                    "min": min(values),
                    "max": max(values)
                }
            else:
                # Non-numeric metrics
                summary[metric_name] = {
                    "count": len(values),
                    "values": values
                }
        
        return summary
    
    def clear(self):
        """Clear all recorded metrics"""
        self.metrics.clear()
        self.start_times.clear()


def calculate_pass_at_k(results: List[bool], k: int) -> float:
    """
    Calculate pass@k metric.
    
    Args:
        results: List of boolean results (True = pass, False = fail)
        k: Number of attempts to consider
        
    Returns:
        Pass@k rate (probability that at least one of k attempts passes)
    """
    if not results or k <= 0:
        return 0.0
    
    # Take first k results
    k_results = results[:k]
    
    # Pass@k = 1 if any of the k results is True, else 0
    return 1.0 if any(k_results) else 0.0


def calculate_success_rates(results: List[Dict[str, Any]]) -> Dict[str, float]:
    """
    Calculate various success rates from evaluation results.
    
    Args:
        results: List of evaluation result dictionaries
        
    Returns:
        Dictionary of success rates
    """
    if not results:
        return {}
    
    total = len(results)
    rates = {}
    
    # Overall success rate
    overall_success = sum(1 for r in results if r.get("overall", {}).get("successful", False))
    rates["overall"] = overall_success / total
    
    # Generation success rate (if available)
    generation_success = sum(1 for r in results if r.get("generation", {}).get("successful", False))
    if generation_success > 0:
        rates["generation"] = generation_success / total
    
    # Compilation success rate (if available)
    compilation_success = sum(1 for r in results if r.get("compilation", {}).get("successful", False))
    if compilation_success > 0:
        rates["compilation"] = compilation_success / total
    
    return rates