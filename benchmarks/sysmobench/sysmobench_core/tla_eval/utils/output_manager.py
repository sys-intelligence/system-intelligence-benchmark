"""
Output Directory Management Module

This module manages the organization of benchmark results using a structured
directory hierarchy with timestamps to prevent overwrites and enable
chronological result tracking.

Structure: output/{metric}/{task}/{method}_{model}/{timestamp}/
"""

import os
import json
from datetime import datetime
from pathlib import Path
from typing import Dict, Any, Optional, List
import logging

logger = logging.getLogger(__name__)


class OutputManager:
    """
    Manages output directory structure and result organization.
    """
    
    def __init__(self, base_output_dir: str = "output"):
        """
        Initialize output manager.
        
        Args:
            base_output_dir: Base directory for all outputs
        """
        self.base_output_dir = Path(base_output_dir)
        self.base_output_dir.mkdir(exist_ok=True)
    
    def create_experiment_dir(self, metric: str, task: str, method: str, model: str, 
                            timestamp: Optional[str] = None) -> Path:
        """
        Create experiment directory with timestamp-based structure.
        
        Args:
            metric: Metric name (e.g., "compilation_check", "runtime_check")
            task: Task name (e.g., "etcd", "raft")
            method: Method name (e.g., "agent_based", "direct_call")
            model: Model name (e.g., "claude", "my_yunwu")
            timestamp: Optional custom timestamp (defaults to current time)
            
        Returns:
            Path to created experiment directory
        """
        if timestamp is None:
            timestamp = datetime.now().strftime("%Y%m%d%H%M%S")
        
        # Structure: output/{metric}/{task}/{method}_{model}/{timestamp}/
        experiment_dir = (
            self.base_output_dir / 
            metric / 
            task / 
            f"{method}_{model}" /
            timestamp
        )
        
        experiment_dir.mkdir(parents=True, exist_ok=True)
        logger.info(f"Created experiment directory: {experiment_dir}")
        
        return experiment_dir
    
    def get_latest_experiment_dir(self, metric: str, task: str, 
                                method: Optional[str] = None, 
                                model: Optional[str] = None) -> Optional[Path]:
        """
        Get the latest experiment directory for given metric/task combination.
        
        Args:
            metric: Metric name
            task: Task name
            method: Optional method filter
            model: Optional model filter
            
        Returns:
            Path to latest experiment directory or None if not found
        """
        task_dir = self.base_output_dir / metric / task
        
        if not task_dir.exists():
            return None
        
        if method and model:
            # Look for specific method_model combination
            method_model_dir = task_dir / f"{method}_{model}"
            if not method_model_dir.exists():
                return None
            
            # Get latest timestamp directory within method_model directory
            timestamp_dirs = sorted([d for d in method_model_dir.iterdir() if d.is_dir()], 
                                  key=lambda x: x.name, reverse=True)
            
            return timestamp_dirs[0] if timestamp_dirs else None
        else:
            # Find latest across all method_model combinations
            latest_dir = None
            latest_timestamp = ""
            
            for method_model_dir in task_dir.iterdir():
                if not method_model_dir.is_dir():
                    continue
                
                # Get latest timestamp in this method_model directory
                timestamp_dirs = sorted([d for d in method_model_dir.iterdir() if d.is_dir()], 
                                      key=lambda x: x.name, reverse=True)
                
                if timestamp_dirs and timestamp_dirs[0].name > latest_timestamp:
                    latest_timestamp = timestamp_dirs[0].name
                    latest_dir = timestamp_dirs[0]
            
            return latest_dir
    
    def save_result(self, experiment_dir: Path, result_data: Dict[str, Any], 
                   metadata: Dict[str, Any]) -> None:
        """
        Save experiment result and metadata to the experiment directory.
        
        Args:
            experiment_dir: Path to experiment directory
            result_data: Result data to save
            metadata: Experiment metadata
        """
        # Save result data
        result_file = experiment_dir / "result.json"
        with open(result_file, 'w', encoding='utf-8') as f:
            json.dump(result_data, f, indent=2, default=str)
        
        # Save metadata
        metadata_file = experiment_dir / "metadata.json"
        with open(metadata_file, 'w', encoding='utf-8') as f:
            json.dump(metadata, f, indent=2, default=str)
        
        logger.info(f"Saved results to {experiment_dir}")
    
    def load_result(self, experiment_dir: Path) -> Dict[str, Any]:
        """
        Load experiment result from directory.
        
        Args:
            experiment_dir: Path to experiment directory
            
        Returns:
            Dictionary containing result and metadata
        """
        result_file = experiment_dir / "result.json"
        metadata_file = experiment_dir / "metadata.json"
        
        result = {}
        
        if result_file.exists():
            with open(result_file, 'r', encoding='utf-8') as f:
                result['result'] = json.load(f)
        
        if metadata_file.exists():
            with open(metadata_file, 'r', encoding='utf-8') as f:
                result['metadata'] = json.load(f)
        
        return result
    
    def list_experiments(self, metric: Optional[str] = None, 
                        task: Optional[str] = None) -> List[Dict[str, Any]]:
        """
        List all experiments with optional filtering.
        
        Args:
            metric: Optional metric filter
            task: Optional task filter
            
        Returns:
            List of experiment information dictionaries
        """
        experiments = []
        
        # Determine search paths
        if metric and task:
            search_paths = [self.base_output_dir / metric / task]
        elif metric:
            metric_dir = self.base_output_dir / metric
            search_paths = [metric_dir / task_dir.name for task_dir in metric_dir.iterdir() if task_dir.is_dir()]
        else:
            search_paths = []
            for metric_dir in self.base_output_dir.iterdir():
                if metric_dir.is_dir():
                    for task_dir in metric_dir.iterdir():
                        if task_dir.is_dir():
                            search_paths.append(task_dir)
        
        # Collect experiment information
        for task_path in search_paths:
            if not task_path.exists():
                continue
                
            metric_name = task_path.parent.name
            task_name = task_path.name
            
            # Iterate through method_model directories
            for method_model_dir in task_path.iterdir():
                if not method_model_dir.is_dir():
                    continue
                
                # Parse method_model from directory name
                dir_name = method_model_dir.name
                if '_' in dir_name:
                    method, model = dir_name.rsplit('_', 1)
                else:
                    method, model = dir_name, "unknown"
                
                # Iterate through timestamp directories
                for timestamp_dir in method_model_dir.iterdir():
                    if not timestamp_dir.is_dir():
                        continue
                        
                    timestamp = timestamp_dir.name
                    
                    experiment_info = {
                        'metric': metric_name,
                        'task': task_name,
                        'method': method,
                        'model': model,
                        'timestamp': timestamp,
                        'path': timestamp_dir
                    }
                    
                    # Load metadata if available
                    metadata_file = timestamp_dir / "metadata.json"
                    if metadata_file.exists():
                        try:
                            with open(metadata_file, 'r', encoding='utf-8') as f:
                                experiment_info['metadata'] = json.load(f)
                        except:
                            pass
                    
                    experiments.append(experiment_info)
        
        # Sort by timestamp (newest first)
        experiments.sort(key=lambda x: x['timestamp'], reverse=True)
        return experiments
    
    def clean_old_experiments(self, metric: str, task: str, method: str, model: str, keep_count: int = 10) -> int:
        """
        Clean old experiment directories, keeping only the most recent ones.
        
        Args:
            metric: Metric name
            task: Task name
            method: Method name
            model: Model name
            keep_count: Number of most recent experiments to keep
            
        Returns:
            Number of directories removed
        """
        method_model_dir = self.base_output_dir / metric / task / f"{method}_{model}"
        
        if not method_model_dir.exists():
            return 0
        
        # Get all timestamp directories, sorted by name (chronologically)
        timestamp_dirs = sorted([d for d in method_model_dir.iterdir() if d.is_dir()], 
                              key=lambda x: x.name, reverse=True)
        
        if len(timestamp_dirs) <= keep_count:
            return 0
        
        # Remove old directories
        removed_count = 0
        for old_dir in timestamp_dirs[keep_count:]:
            try:
                import shutil
                shutil.rmtree(old_dir)
                removed_count += 1
                logger.info(f"Removed old experiment directory: {old_dir}")
            except Exception as e:
                logger.warning(f"Failed to remove {old_dir}: {e}")
        
        return removed_count


# Global output manager instance
_output_manager = None

def get_output_manager(base_output_dir: str = "output") -> OutputManager:
    """Get global output manager instance."""
    global _output_manager
    if _output_manager is None:
        _output_manager = OutputManager(base_output_dir)
    return _output_manager