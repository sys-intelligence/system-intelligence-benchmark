"""
Asterinas RingBuffer system implementation for trace generation and conversion.

This module implements the system-specific interfaces for Asterinas RingBuffer
trace generation using REAL kernel tests in Docker containers.
"""

import subprocess
import json
import time
import re
from pathlib import Path
from typing import Dict, Any, List
from datetime import datetime

from ..base import TraceGenerator, TraceConverter, SystemModule


class RingBufferTraceGenerator(TraceGenerator):
    """Asterinas RingBuffer-specific REAL-TIME trace generator implementation using Docker."""

    def __init__(self):
        self.docker_image = "asterinas/asterinas:0.16.0-20250822"
        self.workspace_path = "/workspace"
        self.timeout_seconds = 600  # 10 minutes for full build + test process
        self._cached_traces = {}  # Cache parsed traces to avoid re-running Docker

    def generate_traces(self, config: Dict[str, Any], output_dir: Path, name_prefix: str = "trace") -> List[Dict[str, Any]]:
        """
        Generate REAL runtime traces using Asterinas kernel in Docker container.

        Args:
            config: Configuration for trace generation
            output_dir: Directory where trace files should be saved
            name_prefix: Prefix for trace file names

        Returns:
            List of dictionaries with generation results for each trace
        """
        try:
            # Extract configuration parameters
            test_name = config.get("test_name", "test_rb_trace_basic")
            num_runs = config.get("num_traces", config.get("num_runs", 1))
            scenario_type = config.get("scenario_type", "real_kernel_test")

            print(f"Generating REAL RingBuffer traces using Asterinas kernel test: {test_name}")
            print(f"Number of runs: {num_runs}")
            print(f"Output directory: {output_dir}")

            # Ensure output directory exists
            output_dir.mkdir(parents=True, exist_ok=True)

            # Check Docker availability
            if not self._check_docker_availability():
                return [{
                    "success": False,
                    "error": "Docker is not available or not running",
                    "trace_file": "",
                    "event_count": 0,
                    "duration": 0.0,
                    "metadata": {}
                }]

            # Setup Asterinas repository
            asterinas_path = self._prepare_asterinas_repo()
            if not asterinas_path:
                return [{
                    "success": False,
                    "error": "Failed to prepare Asterinas repository",
                    "trace_file": "",
                    "event_count": 0,
                    "duration": 0.0,
                    "metadata": {}
                }]

            # Generate traces using real kernel tests
            start_time = datetime.now()
            trace_results = []

            # Run kernel test for each requested trace
            for run_id in range(num_runs):
                print(f"Running kernel test {run_id + 1}/{num_runs}...")

                # Create output path for this run using name_prefix
                output_path = output_dir / f"{name_prefix}_{run_id+1:02d}.jsonl"

                result = self._run_real_kernel_test(
                    asterinas_path,
                    test_name,
                    output_path,
                    run_id
                )

                # Add duration for this individual run
                result["duration"] = result.get("execution_time", 0.0)

                if result["success"]:
                    result["metadata"] = {
                        "sync_primitive": "ringbuffer",
                        "source": "asterinas_kernel_real",
                        "test_name": test_name,
                        "generation_mode": scenario_type,
                        "docker_image": self.docker_image,
                        "run_id": run_id
                    }
                    print(f"Successfully generated {result['event_count']} trace events")
                else:
                    result["metadata"] = {"run_id": run_id, "failed": True}
                    print(f"Failed to generate trace for run {run_id + 1}: {result['error']}")

                trace_results.append(result)

            total_duration = (datetime.now() - start_time).total_seconds()
            print(f"Total generation time: {total_duration:.2f}s")

            return trace_results

        except Exception as e:
            return [{
                "success": False,
                "error": f"Real RingBuffer trace generation failed: {str(e)}",
                "trace_file": "",
                "event_count": 0,
                "duration": 0.0,
                "metadata": {}
            }]

    def _check_docker_availability(self) -> bool:
        """Check if Docker is available and running."""
        try:
            result = subprocess.run(
                ["docker", "--version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode != 0:
                print("Docker command failed")
                return False

            # Check if Docker daemon is running
            result = subprocess.run(
                ["docker", "info"],
                capture_output=True,
                text=True,
                timeout=10
            )
            return result.returncode == 0

        except (subprocess.TimeoutExpired, FileNotFoundError):
            print("Docker is not available or not responding")
            return False

    def _prepare_asterinas_repo(self) -> Path:
        """Prepare Asterinas repository for trace generation."""
        try:
            # Use the repository from the data directory
            project_root = Path(__file__).parent.parent.parent.parent.parent
            asterinas_path = project_root / "data" / "repositories" / "asterinas"

            if not asterinas_path.exists():
                print(f"Asterinas repository not found at {asterinas_path}")
                return None

            # Check if it's a valid Asterinas repository
            if not (asterinas_path / "kernel").exists():
                print(f"Invalid Asterinas repository structure at {asterinas_path}")
                return None

            print(f"Using Asterinas repository at {asterinas_path}")
            return asterinas_path

        except Exception as e:
            print(f"Failed to prepare Asterinas repository: {e}")
            return None

    def _run_real_kernel_test(self, asterinas_path: Path, test_name: str, output_path: Path, run_id: int) -> Dict[str, Any]:
        """Run real Asterinas kernel test in Docker container and extract traces."""
        try:
            # Build Docker run command
            docker_cmd = [
                "docker", "run", "--rm",
                "--privileged", "--network", "host",
                "-v", f"{asterinas_path}:/workspace",
                self.docker_image,
                "/bin/bash", "-c",
                f"""
                cd /workspace &&
                export PATH=/nix/store/4zpvbvn0cvmmn9k05b1qgr5xh7i6r9ka-nix-2.31.1/bin:$PATH &&
                echo 'connect-timeout = 60000' >> /etc/nix/nix.conf &&
                make install_osdk &&
                make initramfs &&
                cd kernel &&
                timeout {self.timeout_seconds} cargo osdk test --features tla-trace --target-arch x86_64 --qemu-args="-accel tcg" {test_name} 2>&1
                """
            ]

            print(f"Running Docker command for kernel test...")
            print(f"Test: {test_name}, Timeout: {self.timeout_seconds}s")

            # Run the Docker container with kernel test
            start_time = time.time()
            result = subprocess.run(
                docker_cmd,
                capture_output=True,
                text=True,
                timeout=self.timeout_seconds + 120
            )
            execution_time = time.time() - start_time

            print(f"Docker execution completed in {execution_time:.2f}s")
            print(f"Return code: {result.returncode}")

            # Debug: Save full output
            debug_path = output_path.parent / f"debug_output_{run_id}.txt"
            with open(debug_path, "w") as f:
                f.write(result.stdout)
                if result.stderr:
                    f.write("\n=== STDERR ===\n")
                    f.write(result.stderr)
            print(f"Saved full output to {debug_path}")

            # Extract trace events from the output
            trace_events = self._parse_trace_output(result.stdout)

            if not trace_events:
                print("No trace events found in output")
                print(f"\n=== STDOUT SAMPLE (first 2000 chars) ===")
                print(result.stdout[:2000])
                print(f"\n=== END STDOUT SAMPLE ===\n")
                return {
                    "success": False,
                    "error": f"No trace events extracted from kernel test {test_name}",
                    "execution_time": execution_time
                }

            # Save trace to file
            with open(output_path, 'w') as f:
                f.write(f"# Real-time RingBuffer trace from Asterinas kernel test: {test_name}\n")
                f.write(f"# Run ID: {run_id}, Timestamp: {datetime.now().isoformat()}\n")
                for event in trace_events:
                    f.write(json.dumps(event) + '\n')

            print(f"Saved {len(trace_events)} trace events to {output_path}")

            return {
                "success": True,
                "trace_file": str(output_path),
                "event_count": len(trace_events),
                "execution_time": execution_time,
                "test_name": test_name,
                "run_id": run_id
            }

        except subprocess.TimeoutExpired:
            return {
                "success": False,
                "error": f"Kernel test {test_name} timed out after {self.timeout_seconds}s"
            }
        except Exception as e:
            return {
                "success": False,
                "error": f"Failed to run kernel test {test_name}: {str(e)}"
            }

    def _parse_trace_output(self, output: str) -> List[Dict[str, Any]]:
        """Parse real trace events from Asterinas kernel test output."""
        events = []

        print(f"Parsing output of {len(output)} characters")

        lines = output.split('\n')
        print(f"Processing {len(lines)} lines")

        for line_num, line in enumerate(lines):
            line = line.strip()

            # Skip empty lines
            if not line:
                continue

            # Look for JSON patterns for RingBuffer traces
            # Format: {"seq":N,"action":"Push","actor":"producer","rb":0,"head":H,"tail":T,"capacity":C,"success":true}
            # Use non-capturing group (?:...) to avoid capturing only the boolean value
            json_pattern = r'\{"seq":\d+,"action":"[^"]*","actor":"[^"]*","rb":\d+,"head":\d+,"tail":\d+,"capacity":\d+,"success":(?:true|false)\}'
            matches = re.findall(json_pattern, line)

            for match in matches:
                try:
                    event = json.loads(match)
                    if all(field in event for field in ['seq', 'action', 'actor']):
                        events.append(event)
                        print(f"Line {line_num}: Found event: {event}")
                except json.JSONDecodeError:
                    continue

            # Also try direct JSON parsing if line looks like JSON
            if line.startswith('{"seq":') and '"action":' in line:
                try:
                    event = json.loads(line)
                    if all(field in event for field in ['seq', 'action', 'actor']):
                        events.append(event)
                        print(f"Line {line_num}: Parsed direct JSON: {event}")
                except json.JSONDecodeError:
                    continue

        # Remove duplicates and sort by sequence number
        seen_seqs = set()
        unique_events = []
        for event in events:
            seq = event.get('seq')
            if seq not in seen_seqs:
                seen_seqs.add(seq)
                unique_events.append(event)

        unique_events.sort(key=lambda x: x.get('seq', 0))

        print(f"Parsed {len(unique_events)} unique trace events from kernel output")
        if len(unique_events) > 0:
            print(f"First event: {unique_events[0]}")
            print(f"Last event: {unique_events[-1]}")

        return unique_events

    def get_default_config(self) -> Dict[str, Any]:
        """Get default configuration for REAL RingBuffer trace generation."""
        return {
            "test_name": "test_rb_trace_basic",
            "num_runs": 1,
            "scenario_type": "real_kernel_test",
            "source": "asterinas_kernel_real",
            "enable_tla_trace": True,
            "timeout_seconds": 600
        }

    def get_available_scenarios(self) -> Dict[str, Dict[str, Any]]:
        """Get available real kernel test scenarios for RingBuffer testing."""
        return {
            "basic": {
                "test_name": "test_rb_trace_basic",
                "num_runs": 1,
                "scenario_type": "real_kernel_test",
                "description": "Basic push/pop operations with wrapping"
            },
            "full_buffer": {
                "test_name": "test_rb_trace_full",
                "num_runs": 1,
                "scenario_type": "real_kernel_test",
                "description": "Test full buffer scenarios"
            },
            "slice_ops": {
                "test_name": "test_rb_trace_slice",
                "num_runs": 1,
                "scenario_type": "real_kernel_test",
                "description": "Test push_slice and pop_slice operations"
            },
            "interleaving": {
                "test_name": "test_rb_trace_interleaving",
                "num_runs": 1,
                "scenario_type": "real_kernel_test",
                "description": "Producer-consumer interleaving"
            },
            "randomized": {
                "test_name": "test_rb_trace_randomized",
                "num_runs": 1,
                "scenario_type": "real_kernel_test",
                "description": "Deterministic random operations to diversify traces"
            },
            "all_tests": {
                "test_name": "test_rb_trace",
                "num_runs": 4,
                "scenario_type": "real_kernel_test",
                "description": "Run all 4 test scenarios"
            }
        }


class RingBufferTraceConverter(TraceConverter):
    """RingBuffer-specific trace converter implementation (placeholder)."""

    def convert_trace(self, input_path: Path, output_path: Path) -> Dict[str, Any]:
        """
        Convert RingBuffer trace to TLA+ specification-compatible format.

        Args:
            input_path: Path to the raw RingBuffer trace file
            output_path: Path where converted trace should be saved

        Returns:
            Dictionary with conversion results
        """
        # For now, just copy the file as-is since we're focusing on generation
        try:
            import shutil
            shutil.copy(input_path, output_path)

            # Count events
            event_count = 0
            with open(input_path, 'r') as f:
                for line in f:
                    if line.strip() and not line.startswith('#'):
                        event_count += 1

            return {
                "success": True,
                "input_events": event_count,
                "output_transitions": event_count,
                "output_file": str(output_path)
            }
        except Exception as e:
            return {
                "success": False,
                "error": f"Conversion failed: {str(e)}"
            }


class RingBufferSystemModule(SystemModule):
    """Complete RingBuffer system implementation."""

    def __init__(self):
        self._trace_generator = RingBufferTraceGenerator()
        self._trace_converter = RingBufferTraceConverter()

    def get_trace_generator(self) -> TraceGenerator:
        """Get the RingBuffer trace generator."""
        return self._trace_generator

    def get_trace_converter(self) -> TraceConverter:
        """Get the RingBuffer trace converter."""
        return self._trace_converter

    def get_system_name(self) -> str:
        """Get the system name identifier."""
        return "ringbuffer"


def get_system() -> SystemModule:
    """
    Factory function to get the RingBuffer system implementation.

    This function is called by the system registry to load this system.

    Returns:
        RingBufferSystemModule instance
    """
    return RingBufferSystemModule()
