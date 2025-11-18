"""
Task loader for benchmark test cases.

This module handles loading source code from GitHub repositories
and preparing them as generation tasks with appropriate prompts.
"""

import subprocess
import shutil
from pathlib import Path
from typing import Dict, List, Tuple
import yaml
from ..methods.base import GenerationTask


class TaskLoader:
    """Loads benchmark tasks by cloning repositories and extracting source code."""
    
    def __init__(self, tasks_dir: str = "tla_eval/tasks", cache_dir: str = "data/repositories"):
        """
        Initialize task loader.
        
        Args:
            tasks_dir: Directory containing task definitions
            cache_dir: Directory to cache cloned repositories
        """
        self.tasks_dir = Path(tasks_dir)
        self.cache_dir = Path(cache_dir)
        self.cache_dir.mkdir(parents=True, exist_ok=True)

    def load_task(self, task_name: str, source_file: str = None, traces_folder: str = None,
                  spec_language: str = "tla") -> GenerationTask:
        """
        Load a specific task by name, automatically cloning repository if needed.

        Args:
            task_name: Name of the task (e.g., "etcd")
            source_file: Specific source file path, or None for default
            traces_folder: Path to the folder containing traces, or None if not available
            spec_language: Target specification language ("tla", "alloy", "pat")

        Returns:
            GenerationTask instance with source code and appropriate prompt
        """
        task_dir = self.tasks_dir / task_name
        
        if not task_dir.exists():
            available = self.list_available_tasks()
            raise ValueError(f"Task '{task_name}' not found. Available: {available}")
        
        # Load task metadata
        metadata_file = task_dir / "task.yaml"
        if not metadata_file.exists():
            raise FileNotFoundError(f"Task metadata file not found: {metadata_file}")
        
        with open(metadata_file, 'r', encoding='utf-8') as f:
            metadata = yaml.safe_load(f)
        
        # Determine which source file to use
        if source_file is None:
            source_file = metadata['default_source_file']

        traces_folder = traces_folder or metadata.get('traces_folder')
        
        # Find source file info
        source_file_info = None
        for file_info in metadata['source_files']:
            if file_info['path'] == source_file:
                source_file_info = file_info
                break
        
        if source_file_info is None:
            available_files = [f['path'] for f in metadata['source_files']]
            raise ValueError(f"Source file '{source_file}' not found. Available: {available_files}")
        
        # Clone repository and get source code
        source_code = self._get_source_code(metadata['repository'], source_file)

        # Load traces
        if metadata.get('trace_format', None) is None:
            raise ValueError("trace_format must be specified in task.yaml metadata")
        traces = self._get_traces(traces_folder, metadata['trace_format']) if traces_folder else None

        return GenerationTask(
            source_code=source_code,
            traces=traces,
            task_name=task_name,
            system_type=metadata['system_type'],
            language=metadata['language'],
            description=metadata['description'],
            spec_module=metadata.get('specModule', task_name),  # Use specModule from config or task name as fallback
            spec_language=spec_language,  # Target specification language
            # Add additional metadata
            extra_info={
                'file_path': source_file,
                'focus': source_file_info['description'],
                'repository_url': metadata['repository']['url'],
                'trace_format': metadata.get('trace_format'),
                'trace_sample': metadata.get('trace_sample')
            }
        )
    
    def _get_source_code(self, repo_info: Dict, file_path: str) -> str:
        """
        Clone repository if needed and extract source code.
        
        Args:
            repo_info: Repository information from task.yaml
            file_path: Path to source file within repository
            
        Returns:
            Source code content
        """
        repo_url = repo_info['url']
        branch = repo_info.get('branch', 'main')
        
        # Create repository cache directory name from URL
        repo_name = repo_url.split('/')[-1].replace('.git', '')
        repo_cache_dir = self.cache_dir / repo_name
        
        # Clone repository if not already cached
        if not repo_cache_dir.exists():
            print(f"Cloning repository: {repo_url}")
            try:
                # Clone with specific commit if specified
                if 'commit' in repo_info:
                    commit = repo_info['commit']
                    print(f"Using fixed commit: {commit}")
                    subprocess.run([
                        'git', 'clone', repo_url, str(repo_cache_dir)
                    ], check=True, capture_output=True, text=True)
                    subprocess.run([
                        'git', 'checkout', commit
                    ], cwd=repo_cache_dir, check=True, capture_output=True, text=True)
                else:
                    subprocess.run([
                        'git', 'clone', '--depth', '1', 
                        '--branch', branch, 
                        repo_url, str(repo_cache_dir)
                    ], check=True, capture_output=True, text=True)
            except subprocess.CalledProcessError as e:
                raise RuntimeError(f"Failed to clone repository {repo_url}: {e.stderr}")
        
        # Read source file
        source_file_path = repo_cache_dir / file_path
        if not source_file_path.exists():
            raise FileNotFoundError(f"Source file not found in repository: {file_path}")
        
        with open(source_file_path, 'r', encoding='utf-8') as f:
            return f.read()
        
    def _get_traces(self, traces_folder: str, trace_format: str) -> List[List[Tuple[str, str]] | Tuple[str, str]]:
        """
        Load execution traces from the specified folder.
        
        Args:
            traces_folder: Path to the folder containing trace files
        
        Returns:
            List of list of traces, where each sublist is a set of distributed traces (TraceLink-based) OR
            List of traces, where each trace records a distributed execution (Etcd or Asterinas-based)
        
        Raises:
            FileNotFoundError: If traces folder or files are not found
        """
        traces_path = Path(traces_folder)
        if not traces_path.exists() or not traces_path.is_dir():
            # Return empty list if traces folder doesn't exist - traces are optional
            return []
        
        if trace_format == "tracelink_based":
            all_traces = []
            for subfolder in traces_path.iterdir():
                if subfolder.is_dir():
                    trace_files = sorted(subfolder.glob("*.txt"))
                    if not trace_files:
                        continue
                    
                    distributed_trace = []
                    for trace_file in trace_files:
                        with open(trace_file, 'r', encoding='utf-8') as f:
                            trace_content = f.read().strip()
                            if trace_content:
                                distributed_trace.append((trace_file.name, trace_content))
                    
                    if distributed_trace:
                        all_traces.append(distributed_trace)
            return all_traces
        if trace_format == "redisraft_based":
            all_traces = []
            for subfolder in sorted([p for p in traces_path.iterdir() if p.is_dir()]):
                merged_trace = subfolder / "merged_trace.ndjson"
                if not merged_trace.is_file():
                    continue
                trace_content = merged_trace.read_text(encoding="utf-8").strip()
                if trace_content:
                    trace_name = f"{subfolder.name}/{merged_trace.name}"
                    all_traces.append((trace_name, trace_content))
            if not all_traces:
                # Return empty list instead of raising error - traces are optional
                return []
            return all_traces
        else:
            all_traces = []
            patterns = [
                "etcd_trace_*.ndjson",
                "trace_*.jsonl",
                "trace-*.ndjson",
                "*_combined.jsonl",
                "traces_summary.json",
            ]
            trace_files = sorted({f for pat in patterns for f in Path(traces_folder).glob(pat)})
            if not trace_files:
                # Return empty list if no trace files found - traces are optional
                return []
            
            for trace_file in trace_files:
                with open(trace_file, 'r', encoding='utf-8') as f:
                    trace_content = f.read().strip()
                    if trace_content:
                        all_traces.append((trace_file.name, trace_content))
            return all_traces

    def get_task_prompt(self, task_name: str, method_name: str, language: str = "tla") -> str:
        """
        Get the appropriate prompt template for a task and method.

        Supports language-specific prompts with fallback to default.
        Priority: prompts/{language}/{method}.txt -> prompts/{method}.txt

        Args:
            task_name: Name of the task
            method_name: Name of the generation method
            language: Target specification language (tla, alloy, pat)

        Returns:
            Prompt template string

        Raises:
            FileNotFoundError: If prompt file is not found
        """
        task_dir = self.tasks_dir / task_name

        # Normalize language name (remove "+")
        language_normalized = language.lower().replace("+", "")

        # Try language-specific prompt first (e.g., prompts/alloy/agent_based.txt)
        lang_specific_prompt = task_dir / "prompts" / language_normalized / f"{method_name}.txt"
        if lang_specific_prompt.exists():
            with open(lang_specific_prompt, 'r', encoding='utf-8') as f:
                return f.read()

        # Fallback to default prompt (e.g., prompts/agent_based.txt)
        default_prompt = task_dir / "prompts" / f"{method_name}.txt"
        if default_prompt.exists():
            with open(default_prompt, 'r', encoding='utf-8') as f:
                return f.read()

        # Neither found
        raise FileNotFoundError(
            f"Prompt file not found for task='{task_name}', method='{method_name}', language='{language}'. "
            f"Tried: {lang_specific_prompt}, {default_prompt}"
        )
    
    def list_available_tasks(self) -> List[str]:
        """List all available task names."""
        if not self.tasks_dir.exists():
            return []
        
        tasks = []
        for item in self.tasks_dir.iterdir():
            if item.is_dir() and not item.name.startswith('.'):
                # Check if it has task.yaml
                if (item / "task.yaml").exists():
                    tasks.append(item.name)
        
        return sorted(tasks)
    
    def list_task_source_files(self, task_name: str) -> List[Dict]:
        """List all available source files for a task."""
        task_dir = self.tasks_dir / task_name
        metadata_file = task_dir / "task.yaml"
        
        with open(metadata_file, 'r', encoding='utf-8') as f:
            metadata = yaml.safe_load(f)
        
        return metadata['source_files']
    
    def get_task_info(self, task_name: str) -> Dict:
        """Get metadata about a specific task."""
        task_dir = self.tasks_dir / task_name
        metadata_file = task_dir / "task.yaml"
        
        with open(metadata_file, 'r', encoding='utf-8') as f:
            return yaml.safe_load(f)
    
    def clear_cache(self, task_name: str = None):
        """
        Clear repository cache.
        
        Args:
            task_name: Clear cache for specific task, or None for all
        """
        if task_name is None:
            # Clear all cache
            if self.cache_dir.exists():
                shutil.rmtree(self.cache_dir)
                self.cache_dir.mkdir(parents=True, exist_ok=True)
        else:
            # Clear cache for specific task
            task_info = self.get_task_info(task_name)
            repo_url = task_info['repository']['url']
            repo_name = repo_url.split('/')[-1].replace('.git', '')
            repo_cache_dir = self.cache_dir / repo_name
            
            if repo_cache_dir.exists():
                shutil.rmtree(repo_cache_dir)


# Global task loader instance
_task_loader = None

def get_task_loader() -> TaskLoader:
    """Get global task loader instance."""
    global _task_loader
    if _task_loader is None:
        _task_loader = TaskLoader()
    return _task_loader

def load_task(task_name: str, source_file: str = None, traces_folder: str = None,
              spec_language: str = "tla") -> GenerationTask:
    """Convenience function to load a task."""
    return get_task_loader().load_task(task_name, source_file, traces_folder, spec_language)
