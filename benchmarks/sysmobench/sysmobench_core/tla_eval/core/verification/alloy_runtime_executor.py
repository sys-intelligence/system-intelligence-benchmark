"""Helper for invoking the Alloy runtime CLI tools."""

import logging
import os
import subprocess
from pathlib import Path
from typing import Dict, Optional, List


logger = logging.getLogger(__name__)


class AlloyRuntimeExecutor:
    """Runs the AlloyRuntime Java helper and parses its output."""

    def __init__(
        self,
        alloy_jar_path: str = "lib/alloy.jar",
        runtime_class: str = "AlloyRuntime",
        timeout: int = 60,
    ):
        self.alloy_jar = Path(alloy_jar_path)
        if not self.alloy_jar.exists():
            raise FileNotFoundError(f"Alloy JAR not found: {self.alloy_jar}")

        self.runtime_class = runtime_class
        self.timeout = timeout

    def run(self, spec_file: Path, extra_args: Optional[List[str]] = None) -> Dict:
        """Execute AlloyRuntime on the provided specification file."""
        classpath = os.pathsep.join([
            str(self.alloy_jar),
            str(self.alloy_jar.parent),
        ])

        cmd = [
            "java",
            "-cp",
            classpath,
            self.runtime_class,
            str(spec_file.resolve()),
            "--timeout",
            str(self.timeout),
        ]

        if extra_args:
            cmd.extend(extra_args)

        logger.info(f"Running: {' '.join(cmd)}")

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.timeout + 10,
            )
            return self._parse_runtime_output(result.returncode, result.stdout, result.stderr)

        except subprocess.TimeoutExpired:
            logger.error(f"Runtime execution timeout after {self.timeout}s")
            return {
                "success": False,
                "error": f"Timeout after {self.timeout}s",
            }

        except Exception as exc:  # pragma: no cover - defensive logging
            logger.error(f"Failed to run Alloy runtime: {exc}")
            return {
                "success": False,
                "error": f"Cannot run runtime checker: {exc}",
            }

    def _parse_runtime_output(self, returncode: int, stdout: str, stderr: str) -> Dict:
        """Parse AlloyRuntime stdout/stderr to a structured dictionary."""
        commands: List[Dict[str, object]] = []
        total_commands = 0
        successful_commands = 0
        failed_commands = 0

        if returncode in (0, 1):
            lines = stdout.split("\n")
            current_command: Optional[Dict[str, object]] = None

            for raw_line in lines:
                line = raw_line.strip()

                if not line:
                    continue

                if line.startswith("COMMANDS:"):
                    try:
                        total_commands = int(line.split(":", 1)[1].strip())
                    except ValueError:
                        logger.debug(f"Unable to parse COMMANDS line: {line}")

                elif line.startswith("=== COMMAND_"):
                    if current_command:
                        commands.append(current_command)
                    current_command = {}

                elif line.startswith("LABEL:") and current_command is not None:
                    current_command["label"] = line.split(":", 1)[1].strip()

                elif line.startswith("TYPE:") and current_command is not None:
                    current_command["type"] = line.split(":", 1)[1].strip()

                elif line.startswith("RESULT:") and current_command is not None:
                    result_str = line.split(":", 1)[1].strip()
                    current_command["result"] = result_str
                    if "PASS" in result_str.upper():
                        successful_commands += 1
                    else:
                        failed_commands += 1

                elif line.startswith("STATUS:") and current_command is not None:
                    current_command["status"] = line.split(":", 1)[1].strip()

                elif line.startswith("EXEC_TIME:") and current_command is not None:
                    time_str = line.split(":", 1)[1].strip().replace("ms", "")
                    try:
                        current_command["exec_time_ms"] = int(time_str)
                    except ValueError:
                        logger.debug(f"Unable to parse EXEC_TIME line: {line}")

            if current_command:
                commands.append(current_command)

            return {
                "success": returncode == 0,
                "total_commands": total_commands,
                "successful_commands": successful_commands,
                "failed_commands": failed_commands,
                "commands": commands,
            }

        # Any other exit code is treated as an internal error
        return {
            "success": False,
            "error": f"Runtime checker internal error (code {returncode}): {stderr}",
        }

