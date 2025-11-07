"""
Setup CLI for downloading TLA+ tools.

This module provides the entry point for the sysmobench-setup command.
It is a thin wrapper around scripts/setup_tools.py to maintain
compatibility while providing a standard CLI interface.
"""

import sys
import os
from pathlib import Path


def main():
    """
    Entry point for sysmobench-setup command.

    This function wraps the existing setup_tools.py script to provide
    a standard command-line interface for downloading and setting up
    TLA+ tools (tla2tools.jar and CommunityModules-deps.jar).
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

        # Import and run the main function from setup_tools.py
        from setup_tools import main as setup_main
        setup_main()

    finally:
        # Restore original working directory
        os.chdir(original_cwd)


if __name__ == '__main__':
    main()
