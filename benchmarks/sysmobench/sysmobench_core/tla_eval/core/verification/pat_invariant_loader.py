"""
PAT Invariant Template Loader: Loads invariant templates from YAML files.

This module provides functionality to load expert-written invariant templates
for PAT/CSP specifications from YAML files.
"""

import logging
import yaml
from pathlib import Path
from typing import List
from dataclasses import dataclass

logger = logging.getLogger(__name__)


@dataclass
class PATInvariantTemplate:
    """Represents a single PAT invariant template from the YAML file"""
    name: str
    type: str  # "safety" or "liveness"
    natural_language: str
    formal_description: str
    csp_example: str


class PATInvariantTemplateLoader:
    """Loads PAT invariant templates from YAML files"""

    def __init__(self, templates_dir: str = "data/pat_invariant_templates"):
        """
        Initialize the template loader.

        Args:
            templates_dir: Directory containing PAT invariant templates
        """
        self.templates_dir = Path(templates_dir)
        logger.info(f"PATInvariantTemplateLoader initialized with dir: {self.templates_dir}")

    def load_task_invariants(self, task_name: str) -> List[PATInvariantTemplate]:
        """
        Load invariant templates for a specific task.

        Args:
            task_name: Name of the task (e.g., "spin", "mutex")

        Returns:
            List of PATInvariantTemplate objects

        Raises:
            FileNotFoundError: If the invariants file doesn't exist
        """
        invariants_file = self.templates_dir / task_name / "invariants.yaml"

        if not invariants_file.exists():
            raise FileNotFoundError(
                f"PAT invariants file not found: {invariants_file}\n"
                f"Available tasks: {self._list_available_tasks()}"
            )

        logger.info(f"Loading PAT invariants from: {invariants_file}")

        with open(invariants_file, 'r', encoding='utf-8') as f:
            data = yaml.safe_load(f)

        if not data or 'invariants' not in data:
            raise ValueError(f"Invalid invariants file format: {invariants_file}")

        templates = []
        for inv_data in data.get('invariants', []):
            try:
                template = PATInvariantTemplate(
                    name=inv_data['name'],
                    type=inv_data['type'],
                    natural_language=inv_data['natural_language'],
                    formal_description=inv_data['formal_description'],
                    csp_example=inv_data['csp_example']
                )
                templates.append(template)
            except KeyError as e:
                logger.warning(f"Skipping invalid invariant (missing field {e}): {inv_data.get('name', 'Unknown')}")
                continue

        logger.info(f"Loaded {len(templates)} PAT invariant templates for task: {task_name}")

        # Log metadata if available
        if 'metadata' in data:
            metadata = data['metadata']
            logger.info(
                f"Metadata: {metadata.get('total_invariants', 0)} total, "
                f"{metadata.get('safety_invariants', 0)} safety, "
                f"{metadata.get('liveness_invariants', 0)} liveness"
            )

        return templates

    def _list_available_tasks(self) -> List[str]:
        """
        List all available tasks with invariant templates.

        Returns:
            List of task names
        """
        if not self.templates_dir.exists():
            return []

        tasks = []
        for item in self.templates_dir.iterdir():
            if item.is_dir() and (item / "invariants.yaml").exists():
                tasks.append(item.name)

        return sorted(tasks)

    def get_available_tasks(self) -> List[str]:
        """
        Public method to get available tasks.

        Returns:
            List of task names that have invariant templates
        """
        return self._list_available_tasks()
