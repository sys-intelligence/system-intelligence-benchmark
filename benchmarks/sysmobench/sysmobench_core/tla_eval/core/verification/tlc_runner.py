"""
TLC Runner Module

This module handles running TLC model checker for trace validation.
"""

import os
import subprocess
from pathlib import Path
from typing import Dict, Any

from .tlc_error_classifier import TLCErrorClassifier, TLCErrorInfo

class TLCRunner:
    """
    Handles TLC model checker execution for trace validation.
    """
    
    def __init__(self, tla_tools_jar: str = None):
        if tla_tools_jar is None:
            # Use absolute path to jar file in project root
            from pathlib import Path
            project_root = Path(__file__).parent.parent.parent.parent
            tla_tools_jar = str(project_root / "lib" / "tla2tools.jar")
        self.tla_tools_jar = tla_tools_jar
        self.tlc_available = self._check_tlc_availability()
        self.error_classifier = TLCErrorClassifier()
    
    def _check_tlc_availability(self) -> bool:
        """Check if TLC tools are available."""
        return os.path.exists(self.tla_tools_jar)
    
    def run_verification(self, trace_path: Path, spec_dir: str) -> Dict[str, Any]:
        """
        Run TLC verification of trace against converted specification.
        
        Args:
            trace_path: Path to the trace file
            spec_dir: Directory containing specTrace.tla and specTrace.cfg
            
        Returns:
            Dictionary with verification results
        """
        try:
            # Check if TLC is available
            if not self.tlc_available:
                return {
                    "success": False,
                    "error": f"TLC tools not found at {self.tla_tools_jar}. TLC verification skipped.",
                    "result": "SKIPPED",
                    "details": "TLC tools are not installed. Please install TLA+ tools to enable verification."
                }
            
            spec_dir_path = Path(spec_dir)
            tla_file = spec_dir_path / "specTrace.tla"
            cfg_file = spec_dir_path / "specTrace.cfg"
            
            if not tla_file.exists() or not cfg_file.exists():
                return {
                    "success": False,
                    "error": f"Missing specTrace files in {spec_dir}"
                }
            
            print(f"Running TLC verification...")
            print(f"Trace file: {trace_path}")
            print(f"Spec directory: {spec_dir}")
            
            # Prepare environment variables for TLC
            env = os.environ.copy()
            # Set TRACE_PATH to the absolute path of the converted trace file
            env["TRACE_PATH"] = str(trace_path.resolve())
            print(f"Set TRACE_PATH environment variable to: {trace_path.resolve()}")
            
            # Run TLC with the generated specification
            cmd = [
                "java", "-cp", self.tla_tools_jar,
                "tlc2.TLC",
                "-config", str(cfg_file),
                str(tla_file)
            ]
            
            result = subprocess.run(
                cmd,
                cwd=str(spec_dir_path),
                capture_output=True,
                text=True,
                env=env,
                timeout=600  # 10 minute timeout
            )
            
            # Classify TLC result using error classifier
            error_info = self.error_classifier.classify_tlc_result(
                result.returncode, result.stdout, result.stderr
            )
            
            if error_info.category.value == "success":
                return {
                    "success": True,
                    "result": "PASS",
                    "details": "TLC verification completed successfully",
                    "output": result.stdout,
                    "error_classification": {
                        "category": error_info.category.value,
                        "exit_code": error_info.exit_code,
                        "is_violation": error_info.is_violation,
                        "is_compilation_error": error_info.is_compilation_error,
                        "is_runtime_error": error_info.is_runtime_error
                    }
                }
            else:
                return {
                    "success": False,
                    "result": "FAILED",
                    "error": f"TLC verification failed: {error_info.description or error_info.message}",
                    "details": result.stderr,
                    "output": result.stdout,
                    "error_classification": {
                        "category": error_info.category.value,
                        "exit_code": error_info.exit_code,
                        "error_code": error_info.error_code,
                        "description": error_info.description,
                        "message": error_info.message,
                        "is_violation": error_info.is_violation,
                        "is_compilation_error": error_info.is_compilation_error,
                        "is_runtime_error": error_info.is_runtime_error,
                        "is_fixable": self.error_classifier.is_fixable_error(error_info),
                        "suggested_fixes": self.error_classifier.suggest_fixes(error_info)
                    }
                }
                
        except subprocess.TimeoutExpired:
            return {
                "success": False,
                "error": "TLC verification timed out after 10 minutes"
            }
        except Exception as e:
            return {
                "success": False,
                "error": f"TLC verification error: {str(e)}"
            }

__all__ = ['TLCRunner']