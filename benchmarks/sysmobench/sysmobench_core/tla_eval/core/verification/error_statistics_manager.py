"""
TLC Error Statistics Manager

This module manages long-term statistics of TLA+ specification errors.
It tracks error frequencies across experiments to help understand common
LLM-generated specification issues.
"""

import os
import yaml
import json
from pathlib import Path
from typing import Dict, Any, Optional
from datetime import datetime
import logging
from dataclasses import dataclass

from .tlc_error_classifier import TLCErrorClassifier, TLCErrorInfo, TLCErrorCategory

logger = logging.getLogger(__name__)


@dataclass
class ErrorStatistics:
    """Container for error statistics data"""
    data: Dict[str, Any]
    file_path: Path
    
    def save(self):
        """Save statistics back to file"""
        self.data['metadata']['last_updated'] = datetime.now().isoformat()
        with open(self.file_path, 'w', encoding='utf-8') as f:
            yaml.dump(self.data, f, default_flow_style=False, indent=2)


class ErrorStatisticsManager:
    """
    Manages long-term error statistics for TLA+ specifications.
    
    This class:
    1. Loads/creates global error statistics file
    2. Classifies TLC results 
    3. Updates global statistics (excluding violations)
    4. Creates per-experiment statistics reports
    5. Provides analysis and reporting
    """
    
    def __init__(self, stats_file_path: str = None):
        """
        Initialize error statistics manager.
        
        Args:
            stats_file_path: Path to global statistics file. If None, uses default location.
        """
        if stats_file_path is None:
            # Default location in the output directory
            project_root = Path(__file__).parent.parent.parent.parent
            output_dir = project_root / "output"
            output_dir.mkdir(exist_ok=True)
            stats_file_path = output_dir / "global_error_statistics.yaml"
        
        self.global_stats_file_path = Path(stats_file_path)
        self.classifier = TLCErrorClassifier()
        self.global_stats = self._load_or_create_global_statistics()
        
        # Per-experiment statistics (reset for each experiment)
        self.current_experiment_stats = self._create_empty_experiment_stats()
    
    def _load_or_create_global_statistics(self) -> ErrorStatistics:
        """Load existing global statistics or create from template"""
        if self.global_stats_file_path.exists():
            logger.info(f"Loading existing global error statistics from {self.global_stats_file_path}")
            with open(self.global_stats_file_path, 'r', encoding='utf-8') as f:
                data = yaml.safe_load(f)
        else:
            logger.info(f"Creating new global error statistics file at {self.global_stats_file_path}")
            # Load template
            template_path = Path(__file__).parent / "error_statistics_template.yaml"
            with open(template_path, 'r', encoding='utf-8') as f:
                data = yaml.safe_load(f)
            
            # Update metadata
            data['metadata']['created_date'] = datetime.now().isoformat()
            data['metadata']['last_updated'] = datetime.now().isoformat()
            
            # Create parent directory if needed
            self.global_stats_file_path.parent.mkdir(parents=True, exist_ok=True)
            
        return ErrorStatistics(data, self.global_stats_file_path)
    
    def _create_empty_experiment_stats(self) -> Dict[str, Any]:
        """Create empty statistics for current experiment"""
        # Load template
        template_path = Path(__file__).parent / "error_statistics_template.yaml"
        with open(template_path, 'r', encoding='utf-8') as f:
            template_data = yaml.safe_load(f)
        
        # Update metadata for experiment
        template_data['metadata']['created_date'] = datetime.now().isoformat()
        template_data['metadata']['last_updated'] = datetime.now().isoformat()
        template_data['metadata']['description'] = "Per-experiment TLA+ error statistics"
        
        return template_data
    
    def classify_and_record_tlc_result(self, 
                                     exit_code: int, 
                                     stdout: str = "", 
                                     stderr: str = "",
                                     context: str = "compilation") -> TLCErrorInfo:
        """
        Classify TLC result and record statistics (excluding violations).
        
        Args:
            exit_code: TLC process exit code
            stdout: Standard output from TLC
            stderr: Standard error from TLC
            context: Context of execution ("compilation", "runtime", "invariant_check")
            
        Returns:
            TLCErrorInfo with detailed classification
        """
        # Classify the error
        error_info = self.classifier.classify_tlc_result(exit_code, stdout, stderr)
        
        # Only record statistics if NOT in special contexts
        # - invariant_check: violations are expected findings, not errors
        # - action_decomposition: internal validation during individual action decomposition
        if context not in ["invariant_check", "action_decomposition"]:
            self._update_global_statistics(error_info)
            self._update_experiment_statistics(error_info)
        else:
            logger.debug(f"Skipping statistics update for context '{context}': {error_info.category.value}")
        
        return error_info
    
    def _update_global_statistics(self, error_info: TLCErrorInfo):
        """Update global error statistics with new error info"""
        try:
            # Ensure data structures exist
            if not hasattr(self.global_stats, 'data') or self.global_stats.data is None:
                logger.error("Global statistics data is None, skipping update")
                return
                
            # Update total runs
            self.global_stats.data['statistics']['total_runs'] += 1
            
            # Update category counters
            if error_info.category == TLCErrorCategory.SUCCESS:
                self.global_stats.data['error_categories']['success'] += 1
                self.global_stats.data['statistics']['successful_runs'] += 1
            elif error_info.is_violation:
                # Violations are findings, not errors - but track them separately
                self.global_stats.data['error_categories']['violations'] += 1
                self.global_stats.data['statistics']['failed_runs'] += 1
                # Also update specific violation code
                if error_info.error_code and error_info.error_code in self.global_stats.data['violation_codes']:
                    self.global_stats.data['violation_codes'][error_info.error_code] += 1
            elif error_info.is_compilation_error:
                self.global_stats.data['error_categories']['compilation_errors'] += 1
                self.global_stats.data['statistics']['failed_runs'] += 1
                self._update_specific_error_code_in_stats(self.global_stats.data, error_info)
            elif error_info.is_runtime_error:
                self.global_stats.data['error_categories']['runtime_errors'] += 1
                self.global_stats.data['statistics']['failed_runs'] += 1
                self._update_specific_error_code_in_stats(self.global_stats.data, error_info)
            else:
                self.global_stats.data['error_categories']['unknown_errors'] += 1
                self.global_stats.data['statistics']['failed_runs'] += 1
            
            # Save global statistics
            self.global_stats.save()
            
            logger.debug(f"Updated global statistics for error {error_info.error_code}: {error_info.category.value}")
            
        except Exception as e:
            logger.error(f"Failed to update global error statistics: {e}")
    
    def _update_experiment_statistics(self, error_info: TLCErrorInfo):
        """Update current experiment statistics with new error info"""
        try:
            # Update total runs
            self.current_experiment_stats['statistics']['total_runs'] += 1
            
            # Update category counters
            if error_info.category == TLCErrorCategory.SUCCESS:
                self.current_experiment_stats['error_categories']['success'] += 1
                self.current_experiment_stats['statistics']['successful_runs'] += 1
            elif error_info.is_violation:
                self.current_experiment_stats['error_categories']['violations'] += 1
                self.current_experiment_stats['statistics']['failed_runs'] += 1
                if error_info.error_code and error_info.error_code in self.current_experiment_stats['violation_codes']:
                    self.current_experiment_stats['violation_codes'][error_info.error_code] += 1
            elif error_info.is_compilation_error:
                self.current_experiment_stats['error_categories']['compilation_errors'] += 1
                self.current_experiment_stats['statistics']['failed_runs'] += 1
                self._update_specific_error_code_in_stats(self.current_experiment_stats, error_info)
            elif error_info.is_runtime_error:
                self.current_experiment_stats['error_categories']['runtime_errors'] += 1
                self.current_experiment_stats['statistics']['failed_runs'] += 1
                self._update_specific_error_code_in_stats(self.current_experiment_stats, error_info)
            else:
                self.current_experiment_stats['error_categories']['unknown_errors'] += 1
                self.current_experiment_stats['statistics']['failed_runs'] += 1
            
            # Update timestamp
            self.current_experiment_stats['metadata']['last_updated'] = datetime.now().isoformat()
            
            logger.debug(f"Updated experiment statistics for error {error_info.error_code}: {error_info.category.value}")
            
        except Exception as e:
            logger.error(f"Failed to update experiment error statistics: {e}")
    
    def _update_specific_error_code_in_stats(self, stats_data: Dict[str, Any], error_info: 'TLCErrorInfo'):
        """Update count for specific error code or SANY error type in given statistics data"""
        # Handle SANY errors (exit code 255 or classified as SANY)
        if (error_info.exit_code == 255 or error_info.is_sany_error) and 'sany_error_types' in stats_data['tlc_error_codes']:
            sany_types = stats_data['tlc_error_codes']['sany_error_types']
            
            if error_info.sany_error_match:
                # Specific SANY error type identified
                error_name = error_info.sany_error_match.error_name
                if error_name in sany_types:
                    sany_types[error_name] += 1
                    logger.debug(f"Incremented SANY error type {error_name}")
                    return
                else:
                    # Fall back to OTHER_SANY_ERROR for unrecognized types
                    if 'OTHER_SANY_ERROR' in sany_types:
                        sany_types['OTHER_SANY_ERROR'] += 1
                        logger.debug(f"Incremented OTHER_SANY_ERROR for unrecognized type {error_name}")
                        return
            else:
                # SANY error but no pattern match - record as OTHER_SANY_ERROR
                if 'OTHER_SANY_ERROR' in sany_types:
                    sany_types['OTHER_SANY_ERROR'] += 1
                    logger.debug(f"Incremented OTHER_SANY_ERROR for unmatched SANY error")
                    return
        
        # Handle regular TLC error codes
        error_code = error_info.error_code
        if not error_code:
            return
            
        # Search through all error code sections
        for section_name, section_data in stats_data['tlc_error_codes'].items():
            if isinstance(section_data, dict) and error_code in section_data:
                section_data[error_code] += 1
                logger.debug(f"Incremented error code {error_code} in section {section_name}")
                return
        
        logger.warning(f"Error code {error_code} not found in statistics template")
    
    def get_global_statistics_summary(self) -> Dict[str, Any]:
        """Get a summary of global error statistics"""
        total_runs = self.global_stats.data['statistics']['total_runs']
        if total_runs == 0:
            return {
                "total_runs": 0, 
                "successful_runs": 0,
                "failed_runs": 0,
                "success_rate": 0.0,
                "error_rate": 0.0,
                "error_categories": self.global_stats.data['error_categories'].copy(),
                "most_common_errors": []
            }
        
        successful_runs = self.global_stats.data['statistics']['successful_runs']
        failed_runs = self.global_stats.data['statistics']['failed_runs']
        
        summary = {
            "total_runs": total_runs,
            "successful_runs": successful_runs,
            "failed_runs": failed_runs,
            "success_rate": successful_runs / total_runs,
            "error_rate": failed_runs / total_runs,
            "error_categories": self.global_stats.data['error_categories'].copy()
        }
        
        # Find most common errors (including SANY error types)
        most_common = []
        for section_name, section_data in self.global_stats.data['tlc_error_codes'].items():
            if isinstance(section_data, dict):
                for code_or_type, count in section_data.items():
                    if count > 0:
                        most_common.append((code_or_type, count, section_name))
        
        # Sort by count descending
        most_common.sort(key=lambda x: x[1], reverse=True)
        summary["most_common_errors"] = most_common[:10]  # Top 10
        
        return summary
    
    def get_experiment_statistics_summary(self) -> Dict[str, Any]:
        """Get a summary of current experiment error statistics"""
        total_runs = self.current_experiment_stats['statistics']['total_runs']
        if total_runs == 0:
            return {
                "total_runs": 0,
                "successful_runs": 0,
                "failed_runs": 0,
                "success_rate": 0.0,
                "error_rate": 0.0,
                "error_categories": self.current_experiment_stats['error_categories'].copy(),
                "most_common_errors": []
            }
        
        successful_runs = self.current_experiment_stats['statistics']['successful_runs']
        failed_runs = self.current_experiment_stats['statistics']['failed_runs']
        
        summary = {
            "total_runs": total_runs,
            "successful_runs": successful_runs,
            "failed_runs": failed_runs,
            "success_rate": successful_runs / total_runs,
            "error_rate": failed_runs / total_runs,
            "error_categories": self.current_experiment_stats['error_categories'].copy()
        }
        
        # Find most common errors in this experiment (including SANY error types)
        most_common = []
        for section_name, section_data in self.current_experiment_stats['tlc_error_codes'].items():
            if isinstance(section_data, dict):
                for code_or_type, count in section_data.items():
                    if count > 0:
                        most_common.append((code_or_type, count, section_name))
        
        # Sort by count descending
        most_common.sort(key=lambda x: x[1], reverse=True)
        summary["most_common_errors"] = most_common[:10]
        
        return summary
    
    def save_experiment_statistics(self, output_dir: Path, 
                                 task_name: str = None,
                                 method_name: str = None,
                                 model_name: str = None) -> Path:
        """
        Save current experiment statistics to output directory.
        
        Args:
            output_dir: Directory to save experiment statistics
            task_name: Optional task name for metadata
            method_name: Optional method name for metadata  
            model_name: Optional model name for metadata
            
        Returns:
            Path to saved statistics file
        """
        # Update metadata with experiment info
        if task_name:
            self.current_experiment_stats['metadata']['task_name'] = task_name
        if method_name:
            self.current_experiment_stats['metadata']['method_name'] = method_name
        if model_name:
            self.current_experiment_stats['metadata']['model_name'] = model_name
        
        # Create output directory if needed
        output_dir = Path(output_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        
        # Save experiment statistics
        stats_file_path = output_dir / "error_statistics.yaml"
        with open(stats_file_path, 'w', encoding='utf-8') as f:
            yaml.dump(self.current_experiment_stats, f, default_flow_style=False, indent=2)
        
        logger.info(f"Saved experiment error statistics to: {stats_file_path}")
        return stats_file_path
    
    def reset_experiment_statistics(self):
        """Reset experiment statistics for a new experiment"""
        self.current_experiment_stats = self._create_empty_experiment_stats()
        logger.debug("Reset experiment statistics for new experiment")
    
    def export_global_statistics(self, format: str = "json") -> str:
        """
        Export statistics in specified format.
        
        Args:
            format: Export format ("json" or "yaml")
            
        Returns:
            Serialized statistics data
        """
        if format.lower() == "json":
            return json.dumps(self.global_stats.data, indent=2, default=str)
        elif format.lower() == "yaml":
            return yaml.dump(self.global_stats.data, default_flow_style=False, indent=2)
        else:
            raise ValueError(f"Unsupported format: {format}")
    
    def export_experiment_statistics(self, format: str = "json") -> str:
        """Export current experiment statistics in specified format."""
        if format.lower() == "json":
            return json.dumps(self.current_experiment_stats, indent=2, default=str)
        elif format.lower() == "yaml":
            return yaml.dump(self.current_experiment_stats, default_flow_style=False, indent=2)
        else:
            raise ValueError(f"Unsupported format: {format}")
    
    def reset_global_statistics(self):
        """Reset all global statistics to zero (useful for testing)"""
        logger.warning("Resetting all global error statistics to zero")
        
        # Reset all counts to 0
        self.global_stats.data['error_categories'] = {k: 0 for k in self.global_stats.data['error_categories']}
        
        # Reset TLC error codes
        for section_data in self.global_stats.data['tlc_error_codes'].values():
            if isinstance(section_data, dict):
                for key in section_data:
                    section_data[key] = 0
        
        # Reset violation codes
        for key in self.global_stats.data['violation_codes']:
            self.global_stats.data['violation_codes'][key] = 0
            
        # Reset statistics
        self.global_stats.data['statistics']['total_runs'] = 0
        self.global_stats.data['statistics']['successful_runs'] = 0
        self.global_stats.data['statistics']['failed_runs'] = 0
        
        # Save
        self.global_stats.save()
    
    def is_violation_error(self, error_info: TLCErrorInfo) -> bool:
        """
        Check if error is a violation (model checking finding) rather than a spec error.
        
        Args:
            error_info: Classified error information
            
        Returns:
            True if this is a violation (not an error)
        """
        return error_info.is_violation
    
    def should_record_error(self, error_info: TLCErrorInfo, context: str) -> bool:
        """
        Determine if this error should be recorded in statistics.
        
        Args:
            error_info: Classified error information
            context: Execution context
            
        Returns:
            True if error should be recorded
        """
        # Never record violations during invariant checking
        if context == "invariant_check" and error_info.is_violation:
            return False
        
        # Record all other cases
        return True


# Singleton instance for global use
_global_stats_manager = None

def get_error_statistics_manager() -> ErrorStatisticsManager:
    """Get the global error statistics manager instance"""
    global _global_stats_manager
    if _global_stats_manager is None:
        _global_stats_manager = ErrorStatisticsManager()
    return _global_stats_manager

def get_experiment_error_statistics_manager() -> ErrorStatisticsManager:
    """Get a new error statistics manager instance for single experiment use"""
    return ErrorStatisticsManager()


# Convenience function for quick classification and recording
def classify_and_record_tlc_result(exit_code: int, 
                                 stdout: str = "", 
                                 stderr: str = "", 
                                 context: str = "compilation") -> TLCErrorInfo:
    """
    Classify TLC result and record statistics using global manager.
    
    Args:
        exit_code: TLC process exit code
        stdout: Standard output from TLC
        stderr: Standard error from TLC  
        context: Execution context ("compilation", "runtime", "invariant_check")
        
    Returns:
        TLCErrorInfo with detailed classification
    """
    manager = get_error_statistics_manager()
    return manager.classify_and_record_tlc_result(exit_code, stdout, stderr, context)