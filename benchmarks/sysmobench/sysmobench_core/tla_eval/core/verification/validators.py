"""
TLA+ specification validator using TLC tools.

This module provides functionality to validate TLA+ specifications using
the TLA tools (SANY parser) to check for compilation errors.
"""

import os
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Tuple, Optional
import logging

from ...utils.setup_utils import get_tla_tools_path, check_java_available
from .error_statistics_manager import classify_and_record_tlc_result, TLCErrorCategory

logger = logging.getLogger(__name__)


class ValidationResult:
    """Result of TLA+ specification validation"""
    
    def __init__(self, success: bool, output: str, 
                 syntax_errors: List[str] = None,
                 semantic_errors: List[str] = None,
                 compilation_time: float = 0.0):
        self.success = success
        self.output = output
        self.syntax_errors = syntax_errors or []
        self.semantic_errors = semantic_errors or []
        self.compilation_time = compilation_time
        
        # Legacy compatibility
        self.errors = self.syntax_errors + self.semantic_errors
    
    def to_dict(self) -> Dict:
        """Convert result to dictionary"""
        return {
            "success": self.success,
            "output": self.output,
            "syntax_errors": self.syntax_errors,
            "semantic_errors": self.semantic_errors,
            "total_errors": len(self.errors),
            "compilation_time": self.compilation_time
        }


class TLAValidator:
    """TLA+ specification validator using SANY"""
    
    def __init__(self, timeout: int = 30, error_stats_manager=None):
        """
        Initialize TLA+ validator.
        
        Args:
            timeout: Timeout for validation in seconds
            error_stats_manager: Optional custom error statistics manager
        """
        self.timeout = timeout
        self.error_stats_manager = error_stats_manager
        self.tla_tools_path = get_tla_tools_path()
        
        # Check prerequisites
        if not self.tla_tools_path.exists():
            raise FileNotFoundError(
                f"TLA+ tools not found at {self.tla_tools_path}. "
                "Run 'python3 -m tla_eval.setup' to download tools."
            )
        
        if not check_java_available():
            raise RuntimeError(
                "Java not found. TLA+ tools require Java to run. "
                "Please install Java and ensure it's in your PATH."
            )
    
    def validate_specification(self, tla_content: str, 
                             module_name: str = None,
                             task_name: str = None,
                             context: str = "compilation") -> ValidationResult:
        """
        Validate a TLA+ specification using SANY.
        
        Args:
            tla_content: TLA+ specification content
            module_name: Optional module name (extracted from content if not provided)
            task_name: Optional task name for organizing saved specifications
            context: Execution context for error statistics (default: "compilation")
            
        Returns:
            ValidationResult with validation outcome
        """
        import time
        
        start_time = time.time()
        
        try:
            # Extract module name if not provided
            if module_name is None:
                module_name = self._extract_module_name(tla_content)
            
            # Create directory for the specification
            # File name must match module name for SANY
            if task_name:
                # Save to organized directory structure
                data_dir = Path.cwd() / "data" / "spec" / task_name
                data_dir.mkdir(parents=True, exist_ok=True)
                spec_file_path = data_dir / f"{module_name}.tla"
            else:
                # Fallback to temporary directory
                import tempfile
                temp_dir = Path(tempfile.gettempdir())
                spec_file_path = temp_dir / f"{module_name}.tla"
            
            with open(spec_file_path, 'w', encoding='utf-8') as spec_file:
                spec_file.write(tla_content)
            
            try:
                # Run SANY validation
                result = self._run_sany_validation(str(spec_file_path), context)
                compilation_time = time.time() - start_time
                
                syntax_errors, semantic_errors = self._parse_errors(result[1]) if not result[0] else ([], [])
                
                return ValidationResult(
                    success=result[0],
                    output=result[1],
                    syntax_errors=syntax_errors,
                    semantic_errors=semantic_errors,
                    compilation_time=compilation_time
                )
                
            finally:
                # Only clean up if using temporary directory
                if not task_name:
                    try:
                        os.unlink(spec_file_path)
                    except:
                        pass
                    
        except Exception as e:
            compilation_time = time.time() - start_time
            logger.error(f"Validation failed: {e}")
            return ValidationResult(
                success=False,
                output=f"Validation error: {e}",
                syntax_errors=[],
                semantic_errors=[str(e)],
                compilation_time=compilation_time
            )
    
    def validate_file(self, file_path: str, context: str = "compilation") -> ValidationResult:
        """
        Validate a TLA+ specification from file.
        
        Args:
            file_path: Path to TLA+ specification file
            context: Execution context for error statistics (default: "compilation")
            
        Returns:
            ValidationResult with validation outcome
        """
        import time
        
        start_time = time.time()
        
        try:
            file_path = Path(file_path)
            if not file_path.exists():
                return ValidationResult(
                    success=False,
                    output=f"File not found: {file_path}",
                    syntax_errors=[f"File not found: {file_path}"],
                    semantic_errors=[],
                    compilation_time=0.0
                )
            
            # Validate the file directly without reading content
            # (SANY validation works on file paths)
            
            # Run SANY validation
            result = self._run_sany_validation(str(file_path), context)
            compilation_time = time.time() - start_time
            
            syntax_errors, semantic_errors = self._parse_errors(result[1]) if not result[0] else ([], [])
            
            return ValidationResult(
                success=result[0],
                output=result[1],
                syntax_errors=syntax_errors,
                semantic_errors=semantic_errors,
                compilation_time=compilation_time
            )
            
        except Exception as e:
            compilation_time = time.time() - start_time
            logger.error(f"File validation failed: {e}")
            return ValidationResult(
                success=False,
                output=f"File validation error: {e}",
                syntax_errors=[],
                semantic_errors=[str(e)],
                compilation_time=compilation_time
            )
    
    def _run_sany_validation(self, file_path: str, context: str = "compilation") -> Tuple[bool, str]:
        """
        Run SANY validation on a TLA+ file.
        
        Args:
            file_path: Path to TLA+ file
            context: Execution context for error statistics
            
        Returns:
            Tuple of (success, output)
        """
        try:
            # Run SANY with standard options
            # Use absolute path and run from project root to avoid path issues
            file_abs_path = Path(file_path).resolve()
            
            cmd = [
                "java",
                "-cp", str(self.tla_tools_path),
                "tla2sany.SANY",
                "-error-codes",
                str(file_abs_path)
            ]
            
            logger.debug(f"Running SANY validation: {' '.join(cmd)}")
            
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.timeout,
                # Run from current working directory instead of file's parent
            )
            
            output = result.stdout + result.stderr
            
            # Use new error classification system instead of string matching
            if self.error_stats_manager:
                # Use custom error statistics manager
                error_info = self.error_stats_manager.classify_and_record_tlc_result(
                    result.returncode,
                    result.stdout,
                    result.stderr, 
                    context=context  # Use passed context parameter
                )
            else:
                # Use global error statistics manager (default behavior)
                error_info = classify_and_record_tlc_result(
                    result.returncode,
                    result.stdout,
                    result.stderr, 
                    context=context  # Use passed context parameter
                )
            
            # Determine success based on classification
            success = error_info.category == TLCErrorCategory.SUCCESS
            
            logger.debug(f"SANY validation result: success={success}, returncode={result.returncode}, output_length={len(output)}")
            
            return success, output
            
        except subprocess.TimeoutExpired:
            return False, f"SANY validation timed out after {self.timeout} seconds"
        except Exception as e:
            return False, f"SANY validation failed: {e}"
    
    def _extract_module_name(self, tla_content: str) -> str:
        """
        Extract module name from TLA+ content.
        
        Args:
            tla_content: TLA+ specification content
            
        Returns:
            Module name or default name
        """
        for line in tla_content.split('\n'):
            line = line.strip()
            # Handle both formats: "---- MODULE Name ----" and "MODULE Name"
            if "---- MODULE" in line:
                try:
                    # Extract content between ---- MODULE and ----
                    return line.split("---- MODULE")[1].split("----")[0].strip()
                except (IndexError, AttributeError):
                    continue
            elif line.startswith("MODULE "):
                try:
                    # Extract module name from "MODULE Name" format
                    return line.split("MODULE ")[1].strip()
                except (IndexError, AttributeError):
                    continue
        return "UnnamedModule"
    
    def _parse_errors(self, output: str) -> Tuple[List[str], List[str]]:
        """
        Simple and direct: return SANY's complete output as error message without any parsing.
        
        Args:
            output: SANY output text
            
        Returns:
            Tuple of (syntax_errors, semantic_errors)
        """
        # Simple and direct: if there are errors, return the entire output as syntax error
        if "Could not parse" in output or "Fatal errors" in output or "*** Errors:" in output:
            return [output.strip()], []
        
        # No errors case
        return [], []


def validate_tla_specification(tla_content: str, 
                             module_name: str = None,
                             timeout: int = 30,
                             context: str = "compilation") -> ValidationResult:
    """
    Convenience function to validate a TLA+ specification.
    
    Args:
        tla_content: TLA+ specification content
        module_name: Optional module name
        timeout: Validation timeout in seconds
        context: Execution context for error statistics
        
    Returns:
        ValidationResult with validation outcome
    """
    validator = TLAValidator(timeout=timeout)
    return validator.validate_specification(tla_content, module_name, context=context)


def validate_tla_file(file_path: str, timeout: int = 30) -> ValidationResult:
    """
    Convenience function to validate a TLA+ specification file.
    
    Args:
        file_path: Path to TLA+ specification file
        timeout: Validation timeout in seconds
        
    Returns:
        ValidationResult with validation outcome
    """
    validator = TLAValidator(timeout=timeout)
    return validator.validate_file(file_path)