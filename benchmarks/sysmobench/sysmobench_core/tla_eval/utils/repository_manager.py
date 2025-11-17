"""
Repository Management Utilities

This module provides utilities for managing source code repositories,
including cloning, patching, and build preparation for trace generation.
"""

import os
import subprocess
import shutil
from pathlib import Path
from typing import Dict, Any, List, Optional
import logging

logger = logging.getLogger(__name__)

class RepositoryManager:
    """
    Manages source code repositories for the TLA+ evaluation framework.
    """
    
    def __init__(self, base_dir: Path = None):
        """
        Initialize repository manager.
        
        Args:
            base_dir: Base directory for repositories (defaults to data/repositories)
        """
        if base_dir is None:
            # Get project root and set default repositories directory
            project_root = Path(__file__).parent.parent.parent
            base_dir = project_root / "data" / "repositories"
        
        self.base_dir = Path(base_dir)
        self.base_dir.mkdir(parents=True, exist_ok=True)
    
    def setup_repository(self, task_config: Dict[str, Any]) -> Path:
        """
        Setup repository for a task, including clone and patch application.
        
        Args:
            task_config: Task configuration dictionary
            
        Returns:
            Path to the prepared repository
            
        Raises:
            Exception: If repository setup fails
        """
        repo_info = task_config.get("repository", {})
        task_name = task_config.get("name", "unknown")
        
        # Determine repository path
        repo_path = self.base_dir / task_name
        
        # Clone or update repository
        if not repo_path.exists():
            logger.info(f"Cloning repository for task '{task_name}'...")
            self._clone_repository(repo_info, repo_path)
        else:
            logger.info(f"Repository for task '{task_name}' already exists")
            self._update_repository(repo_info, repo_path)
        
        # Apply patches if required for Phase 3
        phase3_config = task_config.get("phase3", {})
        if phase3_config.get("patch_required", False):
            self._apply_patches(phase3_config, repo_path, task_name)
        
        return repo_path
    
    def _clone_repository(self, repo_info: Dict[str, Any], repo_path: Path):
        """Clone repository from remote."""
        url = repo_info.get("url")
        if not url:
            raise ValueError("Repository URL not specified in task configuration")
        
        have_submodule = bool(repo_info.get("have_submodule", False))
        # Clone repository
        cmd = ["git", "clone"]
        if have_submodule:
            cmd.append("--recurse-submodules")
        cmd.extend([url, str(repo_path)])
        result = subprocess.run(cmd, capture_output=True, text=True)
        
        if result.returncode != 0:
            raise Exception(f"Failed to clone repository: {result.stderr}")
        
        # Checkout specific version if specified
        self._checkout_version(repo_info, repo_path)

        # Ensure submodules are initialized when requested
        if have_submodule:
            update_cmd = ["git", "submodule", "update", "--init", "--recursive"]
            update_res = subprocess.run(update_cmd, cwd=repo_path, capture_output=True, text=True)
            if update_res.returncode != 0:
                raise Exception(f"Failed to init submodules: {update_res.stderr}")
    
    def _update_repository(self, repo_info: Dict[str, Any], repo_path: Path):
        """Update existing repository."""
        # Check if we need to checkout a different version
        current_commit = self._get_current_commit(repo_path)
        target_commit = repo_info.get("commit")
        
        if target_commit and current_commit != target_commit:
            logger.info(f"Checking out target commit: {target_commit}")
            self._checkout_version(repo_info, repo_path)
    
    def _checkout_version(self, repo_info: Dict[str, Any], repo_path: Path):
        """Checkout specific version (commit, tag, or branch)."""
        # Priority: commit > version > branch
        target = repo_info.get("commit") or repo_info.get("version") or repo_info.get("branch", "main")
        
        cmd = ["git", "checkout", target]
        result = subprocess.run(cmd, cwd=repo_path, capture_output=True, text=True)
        
        if result.returncode != 0:
            raise Exception(f"Failed to checkout {target}: {result.stderr}")
        
        logger.info(f"Checked out {target}")
    
    def _get_current_commit(self, repo_path: Path) -> Optional[str]:
        """Get current commit hash."""
        try:
            cmd = ["git", "rev-parse", "HEAD"]
            result = subprocess.run(cmd, cwd=repo_path, capture_output=True, text=True)
            
            if result.returncode == 0:
                return result.stdout.strip()[:7]  # Short commit hash
        except:
            pass
        return None
    
    def _apply_patches(self, phase3_config: Dict[str, Any], repo_path: Path, task_name: str):
        """Apply patches required for trace generation."""
        patch_file = phase3_config.get("patch_file")
        if not patch_file:
            logger.warning(f"No patch file specified for task '{task_name}'")
            return
        
        # Resolve patch file path
        project_root = Path(__file__).parent.parent.parent
        patch_path = project_root / patch_file
        
        if not patch_path.exists():
            raise FileNotFoundError(f"Patch file not found: {patch_path}")
        
        # Check if patch is already applied
        if self._is_patch_applied(repo_path, patch_path):
            logger.info(f"Patch already applied for task '{task_name}'")
            return
        
        # Apply patch
        logger.info(f"Applying patch: {patch_path}")
        patch_description = phase3_config.get("patch_description", "trace support patch")
        
        cmd = ["git", "apply", str(patch_path)]
        result = subprocess.run(cmd, cwd=repo_path, capture_output=True, text=True)
        
        if result.returncode != 0:
            # Try with --3way for merge conflicts
            cmd = ["git", "apply", "--3way", str(patch_path)]
            result = subprocess.run(cmd, cwd=repo_path, capture_output=True, text=True)
            
            if result.returncode != 0:
                raise Exception(f"Failed to apply patch: {result.stderr}")
        
        logger.info(f"Successfully applied patch: {patch_description}")
    
    def _is_patch_applied(self, repo_path: Path, patch_path: Path) -> bool:
        """Check if patch is already applied by trying to apply it in reverse."""
        cmd = ["git", "apply", "--reverse", "--check", str(patch_path)]
        result = subprocess.run(cmd, cwd=repo_path, capture_output=True, text=True)
        
        return result.returncode == 0
    
    def get_build_environment(self, task_config: Dict[str, Any]) -> Dict[str, str]:
        """
        Get environment variables needed for building with trace support.
        
        Args:
            task_config: Task configuration dictionary
            
        Returns:
            Dictionary of environment variables
        """
        env = os.environ.copy()
        
        # Add build tags for trace support
        phase3_config = task_config.get("phase3", {})
        build_tags = phase3_config.get("build_tags", [])
        
        if build_tags:
            # For Go builds, set build tags
            if task_config.get("language") == "go":
                existing_tags = env.get("GOBUILDTAGS", "")
                all_tags = existing_tags.split(",") if existing_tags else []
                all_tags.extend(build_tags)
                env["GOBUILDTAGS"] = ",".join(all_tags)
        
        return env
    
    def cleanup_repository(self, task_name: str):
        """Remove repository directory."""
        repo_path = self.base_dir / task_name
        if repo_path.exists():
            shutil.rmtree(repo_path)
            logger.info(f"Cleaned up repository for task '{task_name}'")

# Convenience functions
def setup_task_repository(task_config: Dict[str, Any]) -> Path:
    """Setup repository for a task configuration."""
    manager = RepositoryManager()
    return manager.setup_repository(task_config)

def get_task_build_environment(task_config: Dict[str, Any]) -> Dict[str, str]:
    """Get build environment for a task."""
    manager = RepositoryManager()
    return manager.get_build_environment(task_config)

__all__ = ['RepositoryManager', 'setup_task_repository', 'get_task_build_environment']