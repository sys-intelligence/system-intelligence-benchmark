"""
RedisRaft system implementation for trace generation and conversion.

This module implements the system-specific interfaces for RedisRaft
trace generation and format conversion.
"""

import subprocess
import json
import tempfile
import shutil
import os
import time
from pathlib import Path
from typing import Dict, Any, List
from datetime import datetime

from ..base import TraceGenerator, TraceConverter, SystemModule
from .trace_converter_impl import RedisRaftTraceConverterImpl


class RedisRaftTraceGenerator(TraceGenerator):
    """RedisRaft-specific trace generator implementation using existing C program."""

    def __init__(self):
        self.generator_path = Path(__file__).parent / "raft_trace_generator"
        self.output_base = "/home/ubuntu/LLM_Gen_TLA_benchmark_framework/data/sys_traces/redisraft"

    def generate_traces(self, config: Dict[str, Any], output_dir: Path, name_prefix: str = "trace") -> List[Dict[str, Any]]:
        """
        Generate multiple runtime traces using existing RedisRaft C implementation.

        Args:
            config: Configuration for trace generation
            output_dir: Directory where trace files should be saved
            name_prefix: Prefix for trace file names

        Returns:
            List of dictionaries with generation results for each trace
        """
        try:
            # Extract configuration parameters
            num_traces = config.get('num_traces', 20)
            nodes = config.get('nodes', 3)
            duration = config.get('duration_seconds', 15)

            print(f"Generating RedisRaft traces: {num_traces} traces, {nodes} nodes, {duration}s duration")

            # Ensure output directory exists
            output_dir.mkdir(parents=True, exist_ok=True)

            # Check if we have existing traces in the redisraft directory
            existing_traces_dir = Path(self.output_base)
            if existing_traces_dir.exists():
                existing_traces = list(existing_traces_dir.glob("trace_*/merged_trace.ndjson"))
                existing_traces.sort()  # Ensure consistent ordering

                if len(existing_traces) >= num_traces:
                    print(f"Using {num_traces} existing traces from {existing_traces_dir}")
                    return self._use_existing_traces(existing_traces[:num_traces], output_dir, name_prefix)

            # If we don't have enough existing traces, fall back to generation
            print(f"Not enough existing traces found, generating new ones...")
            return self._generate_new_traces(config, output_dir, name_prefix, num_traces, nodes, duration)

        except Exception as e:
            return [{
                "success": False,
                "error": f"RedisRaft trace generation failed: {str(e)}",
                "trace_file": "",
                "event_count": 0,
                "duration": 0.0,
                "metadata": {}
            }]

    def _use_existing_traces(self, existing_traces: List[Path], output_dir: Path, name_prefix: str) -> List[Dict[str, Any]]:
        """Use existing traces from the redisraft directory."""
        results = []

        for i, existing_trace in enumerate(existing_traces):
            # Create output path
            output_path = output_dir / f"{name_prefix}_{i+1:02d}.ndjson"

            try:
                # Copy the existing trace to the output directory
                shutil.copy2(existing_trace, output_path)

                # Count events in the trace
                event_count = 0
                with open(output_path, 'r') as f:
                    for line in f:
                        line = line.strip()
                        if line and line.startswith('{'):
                            try:
                                json.loads(line)
                                event_count += 1
                            except json.JSONDecodeError:
                                pass

                results.append({
                    "success": True,
                    "trace_file": str(output_path),
                    "event_count": event_count,
                    "duration": 0.1,  # Minimal time for copying
                    "metadata": {
                        "source": "existing_trace",
                        "original_path": str(existing_trace),
                        "sync_primitive": "raft_consensus",
                        "nodes": 3,
                        "generation_mode": "c_program_cached"
                    }
                })

                print(f"  Used existing trace {i+1}: {event_count} events from {existing_trace.parent.name}")

            except Exception as e:
                results.append({
                    "success": False,
                    "error": f"Failed to copy existing trace: {str(e)}",
                    "trace_file": str(output_path),
                    "event_count": 0,
                    "duration": 0.0,
                    "metadata": {"failed": True}
                })
                print(f"  Failed to copy trace {i+1}: {str(e)}")

        return results

    def _generate_new_traces(self, config: Dict[str, Any], output_dir: Path, name_prefix: str,
                           num_traces: int, nodes: int, duration: int) -> List[Dict[str, Any]]:
        """Generate new traces using the C program."""
        results = []

        # Check if generator exists
        if not self.generator_path.exists():
            print(f"RedisRaft generator not found at {self.generator_path}, attempting to build...")

            # Try to build the generator
            build_result = self._build_generator()
            if not build_result:
                return [{
                    "success": False,
                    "error": "Failed to build RedisRaft trace generator",
                    "trace_file": "",
                    "event_count": 0,
                    "duration": 0.0,
                    "metadata": {}
                }] * num_traces

        # Generate traces one by one
        for i in range(num_traces):
            output_path = output_dir / f"{name_prefix}_{i+1:02d}.ndjson"

            print(f"Generating trace {i+1}/{num_traces}...")
            result = self._generate_single_trace(nodes, duration, output_path, i)
            results.append(result)

            if result["success"]:
                print(f"  Generated trace {i+1}: {result['event_count']} events")
            else:
                print(f"  Failed to generate trace {i+1}: {result['error']}")

        return results

    def _build_generator(self) -> bool:
        """Build the RedisRaft trace generator."""
        try:
            generator_dir = self.generator_path.parent

            print(f"Building generator in {generator_dir}")
            result = subprocess.run(
                ["make", "clean"],
                cwd=generator_dir,
                capture_output=True,
                text=True,
                timeout=30
            )

            result = subprocess.run(
                ["make"],
                cwd=generator_dir,
                capture_output=True,
                text=True,
                timeout=120
            )

            if result.returncode == 0 and self.generator_path.exists():
                print("Generator built successfully")
                return True
            else:
                print(f"Generator build failed: {result.stderr}")
                return False

        except Exception as e:
            print(f"Failed to build generator: {str(e)}")
            return False

    def _generate_single_trace(self, nodes: int, duration: int, output_path: Path, run_id: int) -> Dict[str, Any]:
        """Generate a single trace using the C program."""
        try:
            start_time = time.time()

            # Run the trace generator
            result = subprocess.run(
                [str(self.generator_path), str(nodes), str(duration)],
                cwd=self.generator_path.parent,
                capture_output=True,
                text=True,
                timeout=duration + 30  # Add buffer time
            )

            execution_time = time.time() - start_time

            if result.returncode != 0:
                return {
                    "success": False,
                    "error": f"Generator failed with exit code {result.returncode}",
                    "trace_file": str(output_path),
                    "event_count": 0,
                    "duration": execution_time,
                    "metadata": {"run_id": run_id, "failed": True}
                }

            # Look for the generated merged trace
            merged_trace = Path("/tmp/raft_traces/merged_trace.ndjson")
            if not merged_trace.exists():
                return {
                    "success": False,
                    "error": "Generator completed but no merged trace found",
                    "trace_file": str(output_path),
                    "event_count": 0,
                    "duration": execution_time,
                    "metadata": {"run_id": run_id, "failed": True}
                }

            # Copy the trace to the output location
            shutil.copy2(merged_trace, output_path)

            # Count events
            event_count = 0
            with open(output_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line and line.startswith('{'):
                        try:
                            json.loads(line)
                            event_count += 1
                        except json.JSONDecodeError:
                            pass

            return {
                "success": True,
                "trace_file": str(output_path),
                "event_count": event_count,
                "duration": execution_time,
                "metadata": {
                    "sync_primitive": "raft_consensus",
                    "nodes": nodes,
                    "duration_seconds": duration,
                    "generation_mode": "c_program_fresh",
                    "run_id": run_id
                }
            }

        except subprocess.TimeoutExpired:
            return {
                "success": False,
                "error": f"Generator timed out after {duration + 30}s",
                "trace_file": str(output_path),
                "event_count": 0,
                "duration": duration + 30,
                "metadata": {"run_id": run_id, "failed": True}
            }
        except Exception as e:
            return {
                "success": False,
                "error": f"Generator execution failed: {str(e)}",
                "trace_file": str(output_path),
                "event_count": 0,
                "duration": 0.0,
                "metadata": {"run_id": run_id, "failed": True}
            }

    def generate_trace(self, config: Dict[str, Any], output_path: Path) -> Dict[str, Any]:
        """
        Generate single runtime trace using RedisRaft C implementation.

        Args:
            config: Configuration for trace generation
            output_path: Path where trace file should be saved

        Returns:
            Dictionary with generation results
        """
        # Use the multi-trace method with count=1
        results = self.generate_traces(config, output_path.parent, output_path.stem)

        if results and len(results) > 0:
            return results[0]
        else:
            return {
                "success": False,
                "error": "Failed to generate single trace",
                "trace_file": str(output_path),
                "event_count": 0,
                "duration": 0.0,
                "metadata": {}
            }

    def get_default_config(self) -> Dict[str, Any]:
        """Get default configuration for RedisRaft trace generation."""
        return {
            "nodes": 3,
            "duration_seconds": 15,
            "num_traces": 20,
            "scenario": "raft_consensus",
            "source": "redisraft_c_program",
            "timeout_seconds": 600
        }

    def get_available_scenarios(self) -> Dict[str, Dict[str, Any]]:
        """Get available predefined scenarios for RedisRaft."""
        return {
            "consensus_basic": {
                "nodes": 3,
                "duration_seconds": 10,
                "num_traces": 20,
                "description": "Basic Raft consensus with leader election and log replication"
            },
            "consensus_extended": {
                "nodes": 3,
                "duration_seconds": 15,
                "num_traces": 20,
                "description": "Extended Raft consensus with more operations"
            },
            "stress_test": {
                "nodes": 3,
                "duration_seconds": 30,
                "num_traces": 10,
                "description": "Longer duration for stress testing"
            },
            "quick_test": {
                "nodes": 3,
                "duration_seconds": 5,
                "num_traces": 5,
                "description": "Quick test with minimal traces"
            }
        }


class RedisRaftTraceConverter(TraceConverter):
    """RedisRaft-specific trace converter implementation."""

    def __init__(self, spec_path: str = None):
        """Initialize converter with optional spec path for mapping files."""
        self.spec_path = spec_path

    def convert_trace(self, input_path: Path, output_path: Path, spec_path: Path = None) -> Dict[str, Any]:
        """
        Convert RedisRaft system trace to TLA+ specification-compatible format.

        Args:
            input_path: Path to the raw RedisRaft trace file
            output_path: Path where converted trace should be saved
            spec_path: Optional path to spec directory for mapping files

        Returns:
            Dictionary with conversion results
        """
        try:
            print(f"Converting RedisRaft trace from {input_path} to {output_path}")

            # Use spec_path if provided, otherwise use instance spec_path
            effective_spec_path = str(spec_path) if spec_path else self.spec_path

            # Initialize RedisRaft trace converter with spec path
            converter = RedisRaftTraceConverterImpl(spec_path=effective_spec_path)

            # Perform conversion
            result = converter.convert_trace(
                input_trace_path=str(input_path),
                output_trace_path=str(output_path)
            )

            if result["success"]:
                return {
                    "success": True,
                    "input_events": result["input_events"],
                    "output_transitions": result["output_transitions"],
                    "output_file": result["output_file"]
                }
            else:
                return {
                    "success": False,
                    "error": result["error"]
                }

        except Exception as e:
            return {
                "success": False,
                "error": f"RedisRaft trace conversion failed: {str(e)}"
            }

    def generate_mapping(self, spec_file: Path, model_name: str = None, output_path: Path = None) -> Dict[str, Any]:
        """
        Generate mapping configuration using LLM.

        Args:
            spec_file: Path to TLA+ specification file
            model_name: Model to use for generation
            output_path: Where to save the mapping file

        Returns:
            Dictionary with generation results
        """
        return RedisRaftTraceConverterImpl.generate_mapping_with_llm(
            spec_file=str(spec_file),
            model_name=model_name,
            output_path=str(output_path) if output_path else None
        )


class RedisRaftSystemModule(SystemModule):
    """Complete RedisRaft system implementation."""

    def __init__(self, spec_path: str = None):
        self._trace_generator = RedisRaftTraceGenerator()
        self._trace_converter = RedisRaftTraceConverter(spec_path=spec_path)
        self.spec_path = spec_path

    def get_trace_generator(self) -> TraceGenerator:
        """Get the RedisRaft trace generator."""
        return self._trace_generator

    def get_trace_converter(self) -> TraceConverter:
        """Get the RedisRaft trace converter."""
        return self._trace_converter

    def get_system_name(self) -> str:
        """Get the system name identifier."""
        return "redisraft"


def get_system() -> SystemModule:
    """
    Factory function to get the RedisRaft system implementation.

    This function is called by the system registry to load this system.

    Returns:
        RedisRaftSystemModule instance
    """
    return RedisRaftSystemModule()