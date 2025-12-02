"""
Formal Verification Tools Setup Script

This script downloads and installs the required formal verification tools:
- TLA+ tools (tla2tools.jar, CommunityModules)
- Alloy Analyzer (alloy.jar)
- PAT (Process Analysis Toolkit)

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
    get_alloy_jar_path,
    get_pat_console_path,
    check_java_available,
    check_mono_available,
    validate_tla_tools_setup,
    validate_alloy_setup,
    validate_pat_setup
)

# TLA+ tools URLs
TLA_TOOLS_URL = "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar"
COMMUNITY_MODULES_URL = "https://github.com/tlaplus/CommunityModules/releases/download/202505152026/CommunityModules-deps.jar"

# Alloy Analyzer URL
ALLOY_URL = "https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.1.0/org.alloytools.alloy.dist.jar"

# PAT (Process Analysis Toolkit) URL
# PAT 3.5.1 full distribution (includes PAT.Console.exe)
PAT_ZIP_URL = "https://pat.comp.nus.edu.sg/resources/pat3_5_1/Process%20Analysis%20Toolkit%203.5.1.zip"
# Note: This downloads the full PAT distribution (~50MB), we need to extract PAT.Console.exe
PAT_URL = PAT_ZIP_URL

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


def setup_alloy_tools():
    """Setup Alloy Analyzer by downloading alloy.jar"""
    print_status("Setting up Alloy Analyzer...")

    lib_dir = PROJECT_ROOT / "lib"
    lib_dir.mkdir(exist_ok=True)

    # Download alloy.jar if not exists
    alloy_path = get_alloy_jar_path()
    if not alloy_path.exists():
        if download_file(ALLOY_URL, alloy_path):
            print_success("Alloy Analyzer setup completed successfully")
            return True
        else:
            print_error("Alloy Analyzer setup failed")
            return False
    else:
        print_success("alloy.jar already exists")
        return True


def setup_pat_tools():
    """Setup PAT (Process Analysis Toolkit) by downloading and extracting PAT distribution"""
    print_status("Setting up PAT (Process Analysis Toolkit)...")

    lib_dir = PROJECT_ROOT / "lib"
    lib_dir.mkdir(exist_ok=True)

    # Check if PAT3.Console.exe already exists
    pat_console_path = get_pat_console_path()
    if pat_console_path.exists():
        print_success("PAT3.Console.exe already exists")
        return True

    if PAT_URL is None:
        print_warning("PAT download URL not available")
        print_status("Please manually download PAT from:")
        print_status("  https://pat.comp.nus.edu.sg/")
        print_status(f"  and place PAT3.Console.exe at: {pat_console_path}")
        return False

    # Download PAT ZIP file
    print_status("Downloading PAT distribution (this may take a while, ~50MB)...")
    pat_zip_path = lib_dir / "pat_temp.zip"

    try:
        if not download_file(PAT_URL, pat_zip_path):
            print_error("Failed to download PAT distribution")
            return False

        # Extract PAT distribution from ZIP
        print_status("Extracting PAT distribution...")
        import zipfile

        try:
            with zipfile.ZipFile(pat_zip_path, 'r') as zip_ref:
                # Look for PAT3.Console.exe in the ZIP
                console_files = [f for f in zip_ref.namelist() if 'PAT3.Console.exe' in f]

                if not console_files:
                    print_error("PAT3.Console.exe not found in distribution")
                    print_status("Available files:")
                    for name in zip_ref.namelist()[:20]:  # Show first 20 files
                        print_status(f"  {name}")
                    return False

                console_file = console_files[0]
                print_status(f"Found: {console_file}")

                # Extract entire PAT directory (preserves directory structure)
                # This will create lib/Process Analysis Toolkit 3/PAT3.Console.exe
                zip_ref.extractall(lib_dir)

                # Verify extraction
                if not pat_console_path.exists():
                    print_error(f"Extraction failed - {pat_console_path} not found")
                    return False

                # Make executable on Unix systems
                try:
                    import stat
                    pat_console_path.chmod(pat_console_path.stat().st_mode | stat.S_IEXEC)
                except:
                    pass

                print_success(f"PAT distribution extracted successfully")
                return True

        except zipfile.BadZipFile:
            print_error("Downloaded file is not a valid ZIP archive")
            return False

    finally:
        # Clean up ZIP file
        if pat_zip_path.exists():
            pat_zip_path.unlink()
            print_status("Cleaned up temporary files")

def verify_tools():
    """Verify that all formal verification tools are properly installed"""
    print_status("Verifying formal verification tools installation...")

    all_ready = True

    # Verify TLA+ tools
    print_status("\n--- TLA+ Tools ---")
    validation_results = validate_tla_tools_setup()

    if validation_results["java_available"]:
        print_success(f"Java available: {validation_results['java_version'] or 'version detected'}")
    else:
        print_warning("Java not found - TLA+ and Alloy require Java to run")

    if validation_results["tla_tools_exists"]:
        print_success(f"tla2tools.jar found ({validation_results['tla_tools_size']:,} bytes)")
    else:
        print_error("tla2tools.jar not found or empty")
        all_ready = False

    if validation_results["community_modules_exists"]:
        print_success(f"CommunityModules-deps.jar found ({validation_results['community_modules_size']:,} bytes)")
    else:
        print_warning("CommunityModules-deps.jar not found - optional for advanced features")

    # Verify Alloy tools
    print_status("\n--- Alloy Analyzer ---")
    alloy_results = validate_alloy_setup()

    if alloy_results["alloy_jar_exists"]:
        print_success(f"alloy.jar found ({alloy_results['alloy_jar_size']:,} bytes)")
    else:
        print_warning("alloy.jar not found - required for Alloy evaluation")

    # Verify PAT tools
    print_status("\n--- PAT (Process Analysis Toolkit) ---")
    pat_results = validate_pat_setup()

    if pat_results["mono_available"]:
        print_success(f"Mono available: {pat_results['mono_version'] or 'version detected'}")
    else:
        print_warning("Mono not found - PAT requires Mono to run on Linux")

    if pat_results["pat_console_exists"]:
        print_success(f"PAT.Console.exe found ({pat_results['pat_console_size']:,} bytes)")
    else:
        print_warning("PAT.Console.exe not found - required for PAT evaluation")

    return all_ready

# Functions get_tla_tools_path, get_community_modules_path, and check_java_available
# are now imported from tla_eval.utils.setup_utils to avoid duplication

def main():
    """Main entry point for tools setup command"""
    print_status("Formal Verification Tools Setup")
    print_status("================================")

    try:
        # Check runtime dependencies
        print_status("\n=== Checking Runtime Dependencies ===")
        if not check_java_available():
            print_warning("Java not found. TLA+ and Alloy require Java to run.")
            print_status("Please install Java 11+ and ensure it's in your PATH.")
        else:
            print_success("Java is available")

        if not check_mono_available():
            print_warning("Mono not found. PAT requires Mono to run on Linux.")
            print_status("Install with: sudo apt-get install mono-complete")
        else:
            print_success("Mono is available")

        # Setup all tools
        print_status("\n=== Setting Up Tools ===")
        setup_tla_tools()
        setup_alloy_tools()
        setup_pat_tools()

        # Verify installation
        print_status("\n=== Verification ===")
        if verify_tools():
            print_success("\n✓ Setup completed successfully!")
            print_status("\nTool paths:")
            print_status(f"  TLA+ tools: {get_tla_tools_path()}")
            print_status(f"  Alloy:      {get_alloy_jar_path()}")
            print_status(f"  PAT:        {get_pat_console_path()}")
        else:
            print_warning("\n⚠ Setup completed with warnings")
            print_status("Some tools may not be available")

    except KeyboardInterrupt:
        print_error("\nSetup interrupted by user")
        sys.exit(1)
    except Exception as e:
        print_error(f"\nUnexpected error: {e}")
        import traceback
        traceback.print_exc()
        sys.exit(1)

if __name__ == "__main__":
    main()