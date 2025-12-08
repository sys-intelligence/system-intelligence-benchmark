"""
PAT Validator: Uses PAT Console for specification validation.

This validator calls PAT Console (Process Analysis Toolkit) to perform
syntax validation for CSP specifications.
"""

import logging
import os
import subprocess
import time
from pathlib import Path
from typing import List, Optional
from dataclasses import dataclass

from ...utils.setup_utils import get_pat_console_path

logger = logging.getLogger(__name__)


@dataclass
class ValidationResult:
    """Result of PAT specification validation"""
    success: bool
    output: str
    syntax_errors: List[str]
    semantic_errors: List[str]
    compilation_time: float
    error_message: Optional[str] = None


class PATValidator:
    """
    Validator for PAT/CSP specifications using PAT Console.

    This validator calls PAT Console to perform syntax checking
    and semantic validation on CSP specifications.
    """

    def __init__(self, timeout: int = 30, pat_console_path: Optional[str] = None):
        """
        Initialize PAT validator.

        Args:
            timeout: Validation timeout in seconds
            pat_console_path: Path to PAT3.Console.exe (defaults to auto-detected path)
        """
        self.timeout = timeout

        # Use provided path or auto-detect from setup_utils
        if pat_console_path:
            self.pat_console = Path(pat_console_path)
        else:
            self.pat_console = get_pat_console_path()

        if not self.pat_console.exists():
            raise FileNotFoundError(f"PAT Console not found: {self.pat_console}")

        logger.info(f"PATValidator initialized with {timeout}s timeout (using {self.pat_console})")

    def validate(self, spec_content: str, output_dir: Optional[Path] = None) -> ValidationResult:
        """
        Validate PAT specification using PAT Console.

        Args:
            spec_content: Content of the .csp file
            output_dir: Optional output directory

        Returns:
            ValidationResult with syntax/semantic errors
        """
        start_time = time.time()

        # Create temp file
        if output_dir is None:
            output_dir = Path("/tmp")
        output_dir.mkdir(parents=True, exist_ok=True)

        temp_file = output_dir / "temp_pat_spec.csp"
        try:
            temp_file.write_text(spec_content, encoding='utf-8')
            logger.info(f"Wrote temp PAT file: {temp_file}")

            # Call PAT Console
            result = self._call_pat_console(temp_file)

            # Update compilation time
            result.compilation_time = time.time() - start_time
            return result

        finally:
            # Clean up temp file
            if temp_file.exists():
                temp_file.unlink()

    def validate_file(self, spec_file: Path) -> ValidationResult:
        """
        Validate PAT specification from file.

        Args:
            spec_file: Path to .csp file

        Returns:
            ValidationResult
        """
        start_time = time.time()

        if not spec_file.exists():
            return ValidationResult(
                success=False,
                output=f"File not found: {spec_file}",
                syntax_errors=[f"File not found: {spec_file}"],
                semantic_errors=[],
                compilation_time=0.0
            )

        try:
            result = self._call_pat_console(spec_file)
            result.compilation_time = time.time() - start_time
            return result

        except Exception as e:
            logger.error(f"Validation failed: {e}")
            return ValidationResult(
                success=False,
                output=f"Validation exception: {str(e)}",
                syntax_errors=[f"Internal error: {str(e)}"],
                semantic_errors=[],
                compilation_time=time.time() - start_time
            )

    def _call_pat_console(self, spec_file: Path) -> ValidationResult:
        """
        Call PAT Console and parse results.

        Args:
            spec_file: Path to .csp file

        Returns:
            ValidationResult
        """
        # PAT Console requires both input and output file
        # We'll use a temp file for output
        import tempfile
        output_fd, output_file = tempfile.mkstemp(suffix=".txt", prefix="pat_output_")
        os.close(output_fd)
        output_path = Path(output_file)

        try:
            cmd = [
                "mono",
                str(self.pat_console),
                "-csp",  # CSP module (default)
                str(spec_file.resolve()),
                str(output_path)
            ]

            logger.info(f"Running: {' '.join(cmd)}")

            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.timeout
            )

            # Parse output
            return self._parse_output(result.returncode, result.stdout, result.stderr)

        except subprocess.TimeoutExpired:
            logger.error(f"Validation timeout after {self.timeout}s")
            return ValidationResult(
                success=False,
                output=f"Validation timeout after {self.timeout}s",
                syntax_errors=[],
                semantic_errors=[f"Timeout after {self.timeout}s"],
                compilation_time=float(self.timeout)
            )

        except Exception as e:
            logger.error(f"Failed to run PAT Console: {e}")
            return ValidationResult(
                success=False,
                output=f"Failed to run PAT: {e}",
                syntax_errors=[f"Cannot run PAT: {e}"],
                semantic_errors=[],
                compilation_time=0.0
            )

        finally:
            # Clean up temp output file
            if output_path.exists():
                output_path.unlink()

    def _parse_output(self, returncode: int, stdout: str, stderr: str) -> ValidationResult:
        """
        Parse output from PAT Console.

        IMPORTANT: PAT Console ALWAYS returns exit code 0, even on parsing errors!
        Therefore, we MUST parse the output text to determine success/failure.

        Strategy:
        - Look for "Parsing Error:" in output → Failure
        - Look for other error keywords → Failure
        - Otherwise → Success

        Args:
            returncode: Exit code (always 0 for PAT, not reliable)
            stdout: Standard output
            stderr: Standard error

        Returns:
            ValidationResult
        """
        import re

        syntax_errors = []
        semantic_errors = []
        combined_output = stdout + "\n" + stderr

        # ============================================================
        # Text-based error detection (PAT always returns exit code 0)
        # ============================================================

        # Check for explicit parsing errors
        if "Parsing Error:" in combined_output or "parsing error:" in combined_output.lower():
            logger.warning("PAT validation failed: Parsing error detected")

            # Extract error messages
            for line in combined_output.split('\n'):
                line = line.strip()
                if not line:
                    continue

                line_lower = line.lower()

                # Collect error lines
                if 'parsing error:' in line_lower or 'error' in line_lower:
                    syntax_errors.append(line)

            # Fallback if no specific errors extracted
            if not syntax_errors:
                syntax_errors.append("Parsing error detected (details not available)")

            return ValidationResult(
                success=False,
                output=combined_output,
                syntax_errors=syntax_errors,
                semantic_errors=[],
                compilation_time=0.0
            )

        # Check for other error patterns
        error_keywords = ['error occurred:', 'compilation error', 'syntax error', 'semantic error']
        has_error = any(keyword in combined_output.lower() for keyword in error_keywords)

        if has_error:
            logger.warning("PAT validation failed: Error keyword detected")

            for line in combined_output.split('\n'):
                line = line.strip()
                if not line:
                    continue

                line_lower = line.lower()

                if any(keyword in line_lower for keyword in error_keywords):
                    syntax_errors.append(line)

            return ValidationResult(
                success=False,
                output=combined_output,
                syntax_errors=syntax_errors,
                semantic_errors=[],
                compilation_time=0.0
            )

        # No errors detected - success
        logger.info("PAT validation passed: No errors in output")
        return ValidationResult(
            success=True,
            output=combined_output,
            syntax_errors=[],
            semantic_errors=semantic_errors,
            compilation_time=0.0
        )
