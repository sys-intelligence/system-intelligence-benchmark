"""
Command-line interface for SysMoBench.

This module provides the main entry point for the sysmobench command.
It is a thin wrapper around scripts/run_benchmark.py to maintain
compatibility while providing a standard CLI interface.
"""

import sys
import os
from pathlib import Path


def main():
    """
    Entry point for sysmobench command.

    This function wraps the existing run_benchmark.py script to provide
    a standard command-line interface while maintaining full compatibility
    with the existing codebase.
    """
    # Get project root directory
    project_root = Path(__file__).parent.parent

    # Change to project root to ensure relative paths work correctly
    original_cwd = os.getcwd()
    os.chdir(project_root)

    try:
        # Add scripts directory to path
        scripts_dir = project_root / 'scripts'
        sys.path.insert(0, str(scripts_dir))

        # Import and run the main function from run_benchmark.py
        from run_benchmark import main as run_main
        run_main()

    finally:
        # Restore original working directory
        os.chdir(original_cwd)


if __name__ == '__main__':
    main()
