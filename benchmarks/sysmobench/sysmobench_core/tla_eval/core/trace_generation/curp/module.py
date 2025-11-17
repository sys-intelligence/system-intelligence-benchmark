"""
CURP system implementation for trace generation and conversion.

This module implements the system-specific interfaces for CURP
trace generation and format conversion.
"""

import json
import shutil
import subprocess
import time
from pathlib import Path
from typing import Any, Dict, List

from ..base import TraceGenerator, TraceConverter, SystemModule
from .trace_converter_impl import CurpTraceConverterImpl


class CurpTraceGenerator(TraceGenerator):
    """CURP-specific trace generator implementation using patched Xline."""

    def __init__(self):
        # Project root: .../SysMoBench (tla_eval is parents[3], project root is parents[4])
        project_root = Path(__file__).resolve().parents[4]
        self.output_base = project_root / "data" / "sys_traces" / "curp"

    def generate_traces(self, config: Dict[str, Any], output_dir: Path, name_prefix: str = "trace") -> List[Dict[str, Any]]:
        """
        Generate multiple runtime traces using patched Xline.

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
            op_count = config.get('op_count', 20)

            print(
                f"Generating CURP traces: {num_traces} traces, {nodes} nodes, {op_count} ops")

            # Ensure output directory exists
            output_dir.mkdir(parents=True, exist_ok=True)

            # Check if we have existing traces in the curp directory
            existing_traces_dir = Path(self.output_base)
            if existing_traces_dir.exists():
                existing_traces = sorted(
                    list(existing_traces_dir.glob("trace_*.ndjson")))

                if len(existing_traces) >= num_traces:
                    print(
                        f"Using {num_traces} existing traces from {existing_traces_dir}")
                    return self._use_existing_traces(existing_traces[:num_traces], output_dir, name_prefix)

            # If we don't have enough existing traces, fall back to generation
            print(f"Not enough existing traces found, generating new ones...")
            return self._generate_new_traces(config, output_dir, name_prefix, num_traces, nodes, op_count)

        except Exception as e:
            return [{
                "success": False,
                "error": f"CURP trace generation failed: {str(e)}",
                "trace_file": "",
                "event_count": 0,
                "duration": 0.0,
                "metadata": {}
            }]

    def _use_existing_traces(self, existing_traces: List[Path], output_dir: Path, name_prefix: str) -> List[Dict[str, Any]]:
        """Use existing traces from the curp directory."""
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
                    # todo: what metadata should be added?
                })

                print(
                    f"  Used existing trace {i+1}: {event_count} events from {existing_trace.parent.name}")

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
                             num_traces: int, nodes: int, op_count: int) -> List[Dict[str, Any]]:
        """Generate new traces using the Xline trace generator (cargo run)."""
        results = []

        # Locate Xline repository prepared by RepositoryManager
        project_root = Path(__file__).resolve().parents[4]
        repo_path = project_root / "data" / "repositories" / "curp"

        if not repo_path.exists():
            print(
                f"Xline repository not found at {repo_path}; cannot generate new traces.")
            return [{
                "success": False,
                "error": f"Xline repository not prepared at {repo_path}",
                "trace_file": "",
                "event_count": 0,
                "duration": 0.0,
                "metadata": {}
            }] * num_traces

        # Build the generator binary first
        if not self._build_generator(repo_path):
            return [{
                "success": False,
                "error": "Failed to build CURP trace generator (cargo build)",
                "trace_file": "",
                "event_count": 0,
                "duration": 0.0,
                "metadata": {}
            }] * num_traces

        # Generate traces one by one
        for i in range(num_traces):
            output_path = output_dir / f"{name_prefix}_{i+1:02d}.ndjson"

            print(f"Generating trace {i+1}/{num_traces}...")
            result = self._generate_single_trace(
                repo_path, nodes, op_count, output_path, i)
            results.append(result)

            if result["success"]:
                print(
                    f"  Generated trace {i+1}: {result['event_count']} events")
            else:
                print(f"  Failed to generate trace {i+1}: {result['error']}")

        return results

    def _build_generator(self, repo_path: Path) -> bool:
        """Build the CURP trace generator."""
        try:
            print(
                f"Building CURP generator in {repo_path}, this may take a while...")
            result = subprocess.run(
                ["cargo", "build", "--release", "--bin", "trace_generator"],
                cwd=repo_path,
                capture_output=True,
                text=True,
                timeout=300
            )
            if result.returncode == 0:
                print("Generator built successfully")
                return True
            else:
                print(
                    f"Generator build failed: {result.stderr or result.stdout}")
                return False
        except Exception as e:
            print(f"Failed to build generator: {str(e)}")
            return False

    def _generate_single_trace(self, repo_path: Path, nodes: int, op_count: int, output_path: Path, run_id: int) -> Dict[str, Any]:
        """Generate a single trace using the trace_generator.rs in Xline repo."""
        try:
            start_time = time.time()

            cmd = [
                "cargo", "run", "--release", "--bin", "trace_generator", "--",
                "--nodes", str(nodes),
                "--op-count", str(op_count),
                "--trace-file", str(output_path),
            ]

            result = subprocess.run(
                cmd,
                cwd=repo_path,
                capture_output=True,
                text=True,
                timeout=60
            )

            execution_time = time.time() - start_time

            if result.returncode != 0:
                return {
                    "success": False,
                    "error": f"Generator failed with exit code {result.returncode}: {result.stderr or result.stdout}",
                    "trace_file": str(output_path),
                    "event_count": 0,
                    "duration": execution_time,
                    "metadata": {"run_id": run_id, "failed": True}
                }

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
                # todo: what metadata should be added?
            }

        except subprocess.TimeoutExpired:
            return {
                "success": False,
                "error": "Generator timed out after 60s",
                "trace_file": str(output_path),
                "event_count": 0,
                "duration": 60,
                # todo: what metadata should be added?
            }

        except Exception as e:
            return {
                "success": False,
                "error": f"Generator execution failed: {str(e)}",
                "trace_file": str(output_path),
                "event_count": 0,
                "duration": 0.0,
                # todo: what metadata should be added?
            }

    def generate_trace(self, config: Dict[str, Any], output_path: Path) -> Dict[str, Any]:
        """
        Generate single runtime trace using the patched Xline generator.

        Args:
            config: Configuration for trace generation
            output_path: Path where trace file should be saved

        Returns:
            Dictionary with generation result
        """
        # Use the multi-trace method with count=1
        results = self.generate_traces(
            config, output_path.parent, output_path.stem)

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
        """Get default configuration for CURP trace generation."""
        return {
            "nodes": 3,
            "op_count": 20,
            "num_traces": 20,
            # todo: should we add more parameters?
        }

    def get_available_scenarios(self) -> Dict[str, Dict[str, Any]]:
        """Get available predefined scenarios for CURP."""
        return {
            "replication_basic": {
                "nodes": 3,
                "op_count": 20,
                "num_traces": 20,
                "description": "Basic CURP replication"
            },
            "replication_extended": {
                "nodes": 3,
                "op_count": 50,
                "num_traces": 20,
                "description": "Extended CURP replication"
            },
            "quick_test": {
                "nodes": 3,
                "op_count": 10,
                "num_traces": 5,
                "description": "Quick test with minimal traces"
            }
        }


class CurpTraceConverter(TraceConverter):
    """CURP-specific trace converter implementation."""

    def __init__(self, spec_path: str = None):
        """Initialize converter with optional spec path for mapping files."""
        self.spec_path = spec_path

    def convert_trace(self, input_path: Path, output_path: Path, spec_path: Path = None) -> Dict[str, Any]:
        """
        Convert CURP system trace to TLA+ specification-compatible format.

        Args:
            input_path: Path to the raw CURP trace file
            output_path: Path where converted trace should be saved
            spec_path: Optional path to spec directory for mapping files

        Returns:
            Dictionary with conversion results
        """
        try:
            print(f"Converting CURP trace from {input_path} to {output_path}")

            # Use spec_path if provided, otherwise use instance spec_path
            effective_spec_path = str(
                spec_path) if spec_path else self.spec_path

            # Initialize CURP trace converter with spec path
            converter = CurpTraceConverterImpl(spec_path=effective_spec_path)

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
                "error": f"CURP trace conversion failed: {str(e)}"
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
        return CurpTraceConverterImpl.generate_mapping_with_llm(
            spec_file=str(spec_file),
            model_name=model_name,
            output_path=str(output_path) if output_path else None
        )


class CurpSystemModule(SystemModule):
    """Complete CURP system implementation."""

    def __init__(self, spec_path: str = None):
        self._trace_generator = CurpTraceGenerator()
        self._trace_converter = CurpTraceConverter(spec_path=spec_path)
        self.spec_path = spec_path

    def get_trace_generator(self) -> TraceGenerator:
        """Get the CURP trace generator."""
        return self._trace_generator

    def get_trace_converter(self) -> TraceConverter:
        """Get the CURP trace converter."""
        return self._trace_converter

    def get_system_name(self) -> str:
        """Get the system name identifier."""
        return "curp"


def get_system() -> SystemModule:
    """
    Factory function to get the CURP system implementation.

    This function is called by the system registry to load this system.

    Returns:
        CurpSystemModule instance
    """
    return CurpSystemModule()
