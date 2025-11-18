"""
Alloy Validator: Uses official Alloy API for specification validation.

This validator calls a Java wrapper that uses the Alloy API to perform
complete syntax and semantic validation.
"""

import logging
import os
import subprocess
import time
from pathlib import Path
from typing import List, Optional, Dict, Any
from dataclasses import dataclass
import re

logger = logging.getLogger(__name__)


@dataclass
class ValidationResult:
    """Result of Alloy specification validation"""
    success: bool
    output: str
    syntax_errors: List[str]
    semantic_errors: List[str]
    compilation_time: float
    error_message: Optional[str] = None


@dataclass
class RuntimeResult:
    """Result of Alloy runtime execution (run/check commands)"""
    success: bool
    output: str
    satisfiable: bool
    execution_time: float
    command_results: List[Dict[str, Any]]
    error_message: Optional[str] = None


class AlloyValidator:
    """
    Validator for Alloy specifications using the official Alloy API.

    This validator calls a Java wrapper (AlloyCliValidator) that uses
    the Alloy compiler to perform complete validation.
    """

    def __init__(self, timeout: int = 30, alloy_jar_path: str = "lib/alloy.jar"):
        """
        Initialize Alloy validator.

        Args:
            timeout: Validation timeout in seconds
            alloy_jar_path: Path to alloy.jar
        """
        self.timeout = timeout
        self.alloy_jar = Path(alloy_jar_path)
        self.validator_class = "AlloyCliValidator"
        self.runtime_class = "AlloyRuntime"

        if not self.alloy_jar.exists():
            raise FileNotFoundError(f"Alloy JAR not found: {self.alloy_jar}")

        logger.info(f"AlloyValidator initialized with {timeout}s timeout (using Alloy API)")

    def validate(self, spec_content: str, output_dir: Optional[Path] = None) -> ValidationResult:
        """
        Validate Alloy specification using the official Alloy compiler.

        Args:
            spec_content: Content of the .als file
            output_dir: Optional output directory

        Returns:
            ValidationResult with syntax/semantic errors
        """
        start_time = time.time()

        # Create temp file
        if output_dir is None:
            output_dir = Path("/tmp")
        output_dir.mkdir(parents=True, exist_ok=True)

        temp_file = output_dir / "temp_alloy_spec.als"
        try:
            temp_file.write_text(spec_content, encoding='utf-8')
            logger.info(f"Wrote temp Alloy file: {temp_file}")

            # Call Java validator
            result = self._call_java_validator(temp_file)

            # Update compilation time
            result.compilation_time = time.time() - start_time
            return result

        finally:
            # Clean up temp file
            if temp_file.exists():
                temp_file.unlink()

    def validate_file(self, spec_file: Path, output_dir: Optional[Path] = None) -> ValidationResult:
        """
        Validate Alloy specification from file.

        Args:
            spec_file: Path to .als file
            output_dir: Optional output directory

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
            result = self._call_java_validator(spec_file)
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

    def _call_java_validator(self, spec_file: Path) -> ValidationResult:
        """
        Call Java validator and parse results.

        Args:
            spec_file: Path to .als file

        Returns:
            ValidationResult
        """
        # Build classpath: alloy.jar and directory containing compiled .class
        classpath = os.pathsep.join([
            str(self.alloy_jar),
            str(self.alloy_jar.parent)
        ])

        cmd = [
            "java",
            "-cp", classpath,
            self.validator_class,
            str(spec_file.resolve())
        ]

        logger.info(f"Running: {' '.join(cmd)}")

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.timeout
            )

            # Parse output
            return self._parse_validator_output(result.returncode, result.stdout, result.stderr)

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
            logger.error(f"Failed to run Java validator: {e}")
            return ValidationResult(
                success=False,
                output=f"Failed to run validator: {e}",
                syntax_errors=[f"Cannot run validator: {e}"],
                semantic_errors=[],
                compilation_time=0.0
            )

    def _parse_validator_output(self, returncode: int, stdout: str, stderr: str) -> ValidationResult:
        """
        Parse output from Java validator.

        Args:
            returncode: Exit code
            stdout: Standard output
            stderr: Standard error

        Returns:
            ValidationResult
        """
        syntax_errors = []
        semantic_errors = []
        output_lines = []

        if returncode == 0:
            # Success
            logger.info("Alloy validation passed")
            return ValidationResult(
                success=True,
                output=stdout,
                syntax_errors=[],
                semantic_errors=[],
                compilation_time=0.0  # Will be set by caller
            )

        elif returncode == 1:
            # Compilation error
            logger.warning("Alloy validation failed")

            # Parse error details from stderr
            error_type = None
            error_msg = None
            error_pos = None

            for line in stderr.split('\n'):
                if line.startswith('ERROR_TYPE:'):
                    error_type = line.split(':', 1)[1].strip()
                elif line.startswith('ERROR_MSG:'):
                    error_msg = line.split(':', 1)[1].strip()
                elif line.startswith('ERROR_POS:'):
                    error_pos = line.split(':', 1)[1].strip()

            # Classify error
            if error_type == 'SYNTAX':
                syntax_errors.append(error_msg or stderr)
            elif error_type == 'SEMANTIC':
                semantic_errors.append(error_msg or stderr)
            else:
                # Unknown type, put in syntax errors
                syntax_errors.append(error_msg or stderr)

            return ValidationResult(
                success=False,
                output=stderr,
                syntax_errors=syntax_errors,
                semantic_errors=semantic_errors,
                compilation_time=0.0  # Will be set by caller
            )

        else:
            # Internal error (returncode == 2 or other)
            logger.error(f"Java validator internal error (code {returncode})")
            return ValidationResult(
                success=False,
                output=stderr,
                syntax_errors=[f"Internal validator error: {stderr}"],
                semantic_errors=[],
                compilation_time=0.0
            )
