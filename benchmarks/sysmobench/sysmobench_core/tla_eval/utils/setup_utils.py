"""
Runtime utilities for formal verification tools path resolution and validation.

This module provides functions to locate formal verification tools (TLA+, Alloy, PAT)
and validate runtime requirements. It does NOT handle downloading/installation -
that's handled by scripts/setup_tools.py
"""

from pathlib import Path
import subprocess
from typing import Optional


# Project root directory
_PROJECT_ROOT = Path(__file__).parent.parent.parent


def get_tla_tools_path() -> Path:
    """
    Get the path to tla2tools.jar.
    
    Returns:
        Path to tla2tools.jar file
    """
    return _PROJECT_ROOT / "lib" / "tla2tools.jar"


def get_community_modules_path() -> Path:
    """
    Get the path to CommunityModules-deps.jar.
    
    Returns:
        Path to CommunityModules-deps.jar file
    """
    return _PROJECT_ROOT / "lib" / "CommunityModules-deps.jar"


def check_java_available() -> bool:
    """
    Check if Java is available in the system.
    
    Returns:
        True if Java is available and can be executed, False otherwise
    """
    try:
        result = subprocess.run(
            ['java', '-version'], 
            capture_output=True, 
            text=True,
            timeout=5
        )
        return result.returncode == 0
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
        return False


def get_java_version() -> Optional[str]:
    """
    Get the Java version string.
    
    Returns:
        Java version string if available, None otherwise
    """
    try:
        result = subprocess.run(
            ['java', '-version'], 
            capture_output=True, 
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            # Java version is typically in stderr
            version_output = result.stderr or result.stdout
            for line in version_output.split('\n'):
                if 'version' in line.lower():
                    return line.strip()
        return None
    except:
        return None


def validate_tla_tools_setup() -> dict:
    """
    Validate that all required TLA+ tools are properly set up.

    Returns:
        Dictionary with validation results
    """
    results = {
        "java_available": False,
        "java_version": None,
        "tla_tools_exists": False,
        "tla_tools_size": 0,
        "community_modules_exists": False,
        "community_modules_size": 0,
        "ready": False
    }

    # Check Java
    results["java_available"] = check_java_available()
    results["java_version"] = get_java_version()

    # Check tla2tools.jar
    tla_tools_path = get_tla_tools_path()
    if tla_tools_path.exists():
        results["tla_tools_exists"] = True
        results["tla_tools_size"] = tla_tools_path.stat().st_size

    # Check CommunityModules-deps.jar (optional)
    community_path = get_community_modules_path()
    if community_path.exists():
        results["community_modules_exists"] = True
        results["community_modules_size"] = community_path.stat().st_size

    # Overall readiness
    results["ready"] = (
        results["java_available"] and
        results["tla_tools_exists"] and
        results["tla_tools_size"] > 0
    )

    return results


# ============================================================================
# Alloy Analyzer Support
# ============================================================================

def get_alloy_jar_path() -> Path:
    """
    Get the path to alloy.jar.

    Returns:
        Path to alloy.jar file
    """
    return _PROJECT_ROOT / "lib" / "alloy.jar"


def validate_alloy_setup() -> dict:
    """
    Validate that Alloy Analyzer is properly set up.

    Returns:
        Dictionary with validation results
    """
    results = {
        "java_available": False,
        "java_version": None,
        "alloy_jar_exists": False,
        "alloy_jar_size": 0,
        "ready": False
    }

    # Check Java
    results["java_available"] = check_java_available()
    results["java_version"] = get_java_version()

    # Check alloy.jar
    alloy_path = get_alloy_jar_path()
    if alloy_path.exists():
        results["alloy_jar_exists"] = True
        results["alloy_jar_size"] = alloy_path.stat().st_size

    # Overall readiness
    results["ready"] = (
        results["java_available"] and
        results["alloy_jar_exists"] and
        results["alloy_jar_size"] > 0
    )

    return results


# ============================================================================
# PAT (Process Analysis Toolkit) Support
# ============================================================================

def get_pat_console_path() -> Path:
    """
    Get the path to PAT3.Console.exe.

    Returns:
        Path to PAT3.Console.exe file
    """
    return _PROJECT_ROOT / "lib" / "Process Analysis Toolkit 3" / "PAT3.Console.exe"


def check_mono_available() -> bool:
    """
    Check if Mono is available in the system (required for PAT on Linux).

    Returns:
        True if Mono is available and can be executed, False otherwise
    """
    try:
        result = subprocess.run(
            ['mono', '--version'],
            capture_output=True,
            text=True,
            timeout=5
        )
        return result.returncode == 0
    except (subprocess.TimeoutExpired, FileNotFoundError, OSError):
        return False


def get_mono_version() -> Optional[str]:
    """
    Get the Mono version string.

    Returns:
        Mono version string if available, None otherwise
    """
    try:
        result = subprocess.run(
            ['mono', '--version'],
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            version_output = result.stdout or result.stderr
            for line in version_output.split('\n'):
                if 'version' in line.lower():
                    return line.strip()
        return None
    except:
        return None


def validate_pat_setup() -> dict:
    """
    Validate that PAT is properly set up.

    Returns:
        Dictionary with validation results
    """
    results = {
        "mono_available": False,
        "mono_version": None,
        "pat_console_exists": False,
        "pat_console_size": 0,
        "ready": False
    }

    # Check Mono
    results["mono_available"] = check_mono_available()
    results["mono_version"] = get_mono_version()

    # Check PAT3.Console.exe
    pat_path = get_pat_console_path()
    if pat_path.exists():
        results["pat_console_exists"] = True
        results["pat_console_size"] = pat_path.stat().st_size

    # Overall readiness
    results["ready"] = (
        results["mono_available"] and
        results["pat_console_exists"] and
        results["pat_console_size"] > 0
    )

    return results