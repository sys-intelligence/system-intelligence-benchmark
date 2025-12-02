"""PAT Runtime Executor: Runs PAT Console for model checking and parses results."""

import logging
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Dict, List, Optional

from ...utils.setup_utils import get_pat_console_path

logger = logging.getLogger(__name__)


class PATRuntimeExecutor:
    """
    Executor for PAT Console model checking.

    Runs PAT Console to execute all assertions in a CSP specification
    and parses the structured output.
    """

    def __init__(self, timeout: int = 60, pat_console_path: Optional[str] = None):
        """
        Initialize PAT runtime executor.

        Args:
            timeout: Execution timeout in seconds
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

        logger.info(f"PATRuntimeExecutor initialized with {timeout}s timeout")

    def run(self, spec_file: Path, extra_args: Optional[List[str]] = None) -> Dict:
        """
        Execute PAT Console model checking on the specification file.

        Args:
            spec_file: Path to .csp file
            extra_args: Optional additional arguments for PAT Console

        Returns:
            Dictionary with execution results:
            {
                "success": bool,
                "total_assertions": int,
                "passed_assertions": int,
                "failed_assertions": int,
                "assertions": [
                    {
                        "name": str,
                        "result": "VALID"/"INVALID",
                        "visited_states": int,
                        "transitions": int,
                        "time_used": float,
                        "memory_used": str,
                        "counterexample": str (optional)
                    }
                ],
                "total_time": float,
                "error": str (optional)
            }
        """
        if not spec_file.exists():
            logger.error(f"Spec file not found: {spec_file}")
            return {
                "success": False,
                "error": f"Specification file not found: {spec_file}"
            }

        # Create temporary output file
        output_fd, output_file = tempfile.mkstemp(suffix=".txt", prefix="pat_runtime_")
        os.close(output_fd)
        output_path = Path(output_file)

        try:
            cmd = [
                "mono",
                str(self.pat_console),
                "-csp",  # CSP module
                str(spec_file.resolve()),
                str(output_path)
            ]

            if extra_args:
                cmd.extend(extra_args)

            logger.info(f"Running: {' '.join(cmd)}")

            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.timeout + 10  # Extra buffer for process overhead
            )

            # Read output file
            if output_path.exists():
                output_content = output_path.read_text(encoding='utf-8')
            else:
                output_content = ""

            # Check for parsing errors first
            combined_output = result.stdout + "\n" + result.stderr
            if "Parsing Error:" in combined_output:
                logger.error("PAT parsing error detected")
                return {
                    "success": False,
                    "error": f"Parsing error: {combined_output}"
                }

            # Parse runtime output
            return self._parse_runtime_output(output_content, result.stdout, result.stderr)

        except subprocess.TimeoutExpired:
            logger.error(f"PAT runtime execution timeout after {self.timeout}s")
            return {
                "success": False,
                "error": f"Timeout after {self.timeout}s"
            }

        except Exception as exc:
            logger.error(f"Failed to run PAT runtime: {exc}")
            return {
                "success": False,
                "error": f"Cannot run runtime checker: {exc}"
            }

        finally:
            # Clean up temporary output file
            if output_path.exists():
                output_path.unlink()

    def _parse_runtime_output(self, output_content: str, stdout: str, stderr: str) -> Dict:
        """
        Parse PAT Console output file to structured dictionary.

        PAT output format:
        =======================================================
        Assertion: <assertion_name>
        ********Verification Result********
        The Assertion (...) is VALID/INVALID.

        ********Verification Setting********
        ...

        ********Verification Statistics********
        Visited States:<number>
        Total Transitions:<number>
        Time Used:<time>s
        Estimated Memory Used:<memory>KB

        Args:
            output_content: Content of PAT output file
            stdout: Standard output from PAT Console
            stderr: Standard error from PAT Console

        Returns:
            Parsed result dictionary
        """
        assertions = []
        total_assertions = 0
        passed_assertions = 0
        failed_assertions = 0

        # Split output by assertion sections
        sections = output_content.split("=======================================================")

        failed_assertion_names = []

        for section in sections:
            section = section.strip()
            if not section or "Assertion:" not in section:
                continue

            total_assertions += 1
            assertion_data = self._parse_assertion_section(section)

            if assertion_data:
                assertions.append(assertion_data)
                if assertion_data["result"] == "VALID":
                    passed_assertions += 1
                elif assertion_data["result"] == "INVALID":
                    failed_assertions += 1
                    failed_assertion_names.append(assertion_data.get("name", "Unknown"))

        # Calculate total time
        total_time = sum(a.get("time_used", 0.0) for a in assertions)

        success = failed_assertions == 0

        result = {
            "success": success,
            "total_assertions": total_assertions,
            "passed_assertions": passed_assertions,
            "failed_assertions": failed_assertions,
            "assertions": assertions,
            "total_time": total_time
        }

        if failed_assertions > 0:
            # Provide a concise failure reason for upstream evaluators/logging
            failed_list = ", ".join(failed_assertion_names[:3])
            if failed_assertions > 3:
                failed_list += ", ..."
            result["error"] = (
                f"{failed_assertions} assertion(s) failed: {failed_list or 'Unknown'}"
            )

        logger.info(
            f"PAT runtime result: {passed_assertions}/{total_assertions} assertions passed"
        )

        return result

    def _parse_assertion_section(self, section: str) -> Optional[Dict]:
        """
        Parse a single assertion section.

        Args:
            section: Text of one assertion section

        Returns:
            Dictionary with assertion data or None if parsing failed
        """
        try:
            assertion_data = {}

            # Extract assertion name
            name_match = re.search(r'Assertion:\s*(.+?)(?:\n|\r|$)', section)
            if name_match:
                assertion_data["name"] = name_match.group(1).strip()
            else:
                assertion_data["name"] = "Unknown"

            # Extract verification result (VALID/INVALID)
            if "is VALID" in section:
                assertion_data["result"] = "VALID"
            elif "is INVALID" in section or "is NOT valid" in section:
                assertion_data["result"] = "INVALID"
            else:
                # Unable to determine result
                assertion_data["result"] = "UNKNOWN"

            # Extract statistics
            # Visited States
            states_match = re.search(r'Visited States:\s*(\d+)', section)
            if states_match:
                assertion_data["visited_states"] = int(states_match.group(1))

            # Total Transitions
            transitions_match = re.search(r'Total Transitions:\s*(\d+)', section)
            if transitions_match:
                assertion_data["transitions"] = int(transitions_match.group(1))

            # Time Used (in seconds)
            time_match = re.search(r'Time Used:\s*([\d.]+)\s*s', section)
            if time_match:
                assertion_data["time_used"] = float(time_match.group(1))

            # Estimated Memory Used
            memory_match = re.search(r'Estimated Memory Used:\s*([\d.]+\s*[KMG]?B)', section)
            if memory_match:
                assertion_data["memory_used"] = memory_match.group(1).strip()

            # Extract counterexample if assertion failed
            if assertion_data["result"] == "INVALID":
                # Look for counterexample trace (usually after "The Assertion ... is INVALID")
                # PAT may output trace information - this is a simplified extraction
                ce_section = section.split("********Verification Result********")
                if len(ce_section) > 1:
                    # The counterexample is typically between result and settings
                    potential_ce = ce_section[1].split("********Verification Setting********")[0]
                    # Clean up and store if non-empty
                    ce_text = potential_ce.strip()
                    if ce_text and len(ce_text) > len("The Assertion"):
                        assertion_data["counterexample"] = ce_text

            return assertion_data

        except Exception as e:
            logger.warning(f"Failed to parse assertion section: {e}")
            return None
