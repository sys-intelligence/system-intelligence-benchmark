"""
TLA+ Tools Setup Script

This script downloads and installs the required TLA+ tools for the benchmark framework.
For runtime path resolution, see tla_eval.utils.setup_utils
"""

import os
import sys
import urllib.request
import tempfile
import shutil
from pathlib import Path
import logging

# Setup logging
logging.basicConfig(level=logging.INFO, format='[%(levelname)s] %(message)s')
logger = logging.getLogger(__name__)

# Project root directory
PROJECT_ROOT = Path(__file__).parent.parent

# Add project to path to import our utilities
sys.path.insert(0, str(PROJECT_ROOT))
from tla_eval.utils.setup_utils import (
    get_tla_tools_path, 
    get_community_modules_path, 
    check_java_available,
    validate_tla_tools_setup
)

# TLA+ tools URLs
TLA_TOOLS_URL = "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
COMMUNITY_MODULES_URL = "https://github.com/tlaplus/CommunityModules/releases/download/202505152026/CommunityModules-deps.jar"

def print_status(message: str):
    """Print status message"""
    logger.info(message)

def print_success(message: str):
    """Print success message"""
    logger.info(f"✓ {message}")

def print_warning(message: str):
    """Print warning message"""
    logger.warning(f"⚠ {message}")

def print_error(message: str):
    """Print error message"""
    logger.error(f"✗ {message}")

def download_file(url: str, output_path: Path) -> bool:
    """
    Download a file from URL to output path.
    
    Args:
        url: URL to download from
        output_path: Path to save the file
        
    Returns:
        True if successful, False otherwise
    """
    try:
        print_status(f"Downloading {output_path.name}...")
        
        # Create directory if it doesn't exist
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        # Download with progress
        with tempfile.NamedTemporaryFile(delete=False) as temp_file:
            with urllib.request.urlopen(url) as response:
                # Get file size for progress tracking
                file_size = int(response.headers.get('Content-Length', 0))
                downloaded = 0
                chunk_size = 8192
                
                while True:
                    chunk = response.read(chunk_size)
                    if not chunk:
                        break
                    temp_file.write(chunk)
                    downloaded += len(chunk)
                    
                    if file_size > 0:
                        progress = (downloaded / file_size) * 100
                        print(f"\rProgress: {progress:.1f}%", end='', flush=True)
                
                print()  # New line after progress

            # Move temp file to final location (use shutil.move to handle cross-device)
            shutil.move(temp_file.name, str(output_path))
            print_success(f"{output_path.name} downloaded successfully")
            return True
            
    except Exception as e:
        print_error(f"Failed to download {output_path.name}: {e}")
        return False

def setup_tla_tools():
    """Setup TLA+ tools by downloading required JAR files"""
    print_status("Setting up TLA+ tools...")
    
    lib_dir = PROJECT_ROOT / "lib"
    lib_dir.mkdir(exist_ok=True)
    
    success = True
    
    # Download tla2tools.jar if not exists
    tla_tools_path = get_tla_tools_path()
    if not tla_tools_path.exists():
        if not download_file(TLA_TOOLS_URL, tla_tools_path):
            success = False
    else:
        print_success("tla2tools.jar already exists")
    
    # Download CommunityModules-deps.jar if not exists
    community_modules_path = get_community_modules_path()
    if not community_modules_path.exists():
        if not download_file(COMMUNITY_MODULES_URL, community_modules_path):
            print_warning("CommunityModules-deps.jar download failed - this is optional for basic functionality")
    else:
        print_success("CommunityModules-deps.jar already exists")
    
    if success:
        print_success("TLA+ tools setup completed successfully")
    else:
        print_error("TLA+ tools setup completed with errors")
        sys.exit(1)
    
    return success

def verify_tools():
    """Verify that TLA+ tools are properly installed"""
    print_status("Verifying TLA+ tools installation...")
    
    # Use the comprehensive validation from setup_utils
    validation_results = validate_tla_tools_setup()
    
    # Report Java status
    if validation_results["java_available"]:
        print_success(f"Java available: {validation_results['java_version'] or 'version detected'}")
    else:
        print_warning("Java not found - TLA+ tools require Java to run")
    
    # Report tla2tools.jar status
    if validation_results["tla_tools_exists"]:
        print_success(f"tla2tools.jar found ({validation_results['tla_tools_size']:,} bytes)")
    else:
        print_error("tla2tools.jar not found or empty")
    
    # Report CommunityModules-deps.jar status (optional)
    if validation_results["community_modules_exists"]:
        print_success(f"CommunityModules-deps.jar found ({validation_results['community_modules_size']:,} bytes)")
    else:
        print_warning("CommunityModules-deps.jar not found - optional for advanced features")
    
    return validation_results["ready"]

# Functions get_tla_tools_path, get_community_modules_path, and check_java_available
# are now imported from tla_eval.utils.setup_utils to avoid duplication

def main():
    """Main entry point for tla-setup command"""
    print_status("TLA+ Tools Setup")
    print_status("================")
    
    try:
        # Check Java availability
        if not check_java_available():
            print_warning("Java not found. TLA+ tools require Java to run.")
            print_status("Please install Java and ensure it's in your PATH.")
        
        # Setup tools
        setup_tla_tools()
        
        # Verify installation
        if verify_tools():
            print_success("All tools are ready for use!")
            print_status(f"TLA+ tools path: {get_tla_tools_path()}")
        else:
            print_error("Tool verification failed")
            sys.exit(1)
            
    except KeyboardInterrupt:
        print_error("Setup interrupted by user")
        sys.exit(1)
    except Exception as e:
        print_error(f"Unexpected error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()