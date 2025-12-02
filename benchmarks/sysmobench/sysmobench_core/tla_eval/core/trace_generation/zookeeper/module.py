"""
ZooKeeper system implementation for trace generation and conversion.

This module implements the system-specific interfaces for ZooKeeper
trace generation using the Remix framework and format conversion.
"""

from pathlib import Path
from typing import Dict, Any, List
from datetime import datetime

from ..base import TraceGenerator, TraceConverter, SystemModule
from .cluster import ZooKeeperCluster
from .trace_converter_impl import ZooKeeperTraceConverter


class ZooKeeperTraceGenerator(TraceGenerator):
    """
    ZooKeeper trace generator using Remix infrastructure.

    Quantity Control Strategy:
    1. Generate N*factor model traces with TLC (with redundancy)
    2. Parse all traces to JSON
    3. Replay traces one by one until N successful system traces collected
    4. If insufficient, retry with additional generation
    """

    def __init__(self):
        """Initialize generator with ZooKeeper cluster manager."""
        self.cluster = ZooKeeperCluster()

    def generate_traces(self, config: Dict[str, Any], output_dir: Path,
                       name_prefix: str = "trace") -> List[Dict[str, Any]]:
        """
        Generate specified number of ZooKeeper system traces.

        Args:
            config: Configuration dictionary with keys:
                - num_traces: Number of traces required (default: 3)
                - generation_factor: Redundancy multiplier (default: 1.5)
                - max_attempts: Maximum generation attempts (default: 3)
                - simulation_depth: TLC simulation depth (default: 100)
                - max_crashes: Max node crashes in trace (default: 2)
                - max_epoch: Max ZAB epoch (default: 3)
                - max_transactions: Max transactions (default: 2)
                - max_partitions: Max network partitions (default: 0)
            output_dir: Directory for output NDJSON files
            name_prefix: Prefix for trace filenames

        Returns:
            List of result dictionaries:
            [{
                "success": bool,
                "trace_file": str,
                "event_count": int,
                "replay_time": float,
                "metadata": dict
            }, ...]
        """
        # Extract configuration
        num_traces = config.get('num_traces', 3)
        generation_factor = config.get('generation_factor', 1.5)
        max_attempts = config.get('max_attempts', 3)

        results = []
        attempt = 0

        print(f"Starting ZooKeeper trace generation: target={num_traces} traces")

        while len(results) < num_traces and attempt < max_attempts:
            attempt += 1

            # Calculate how many to generate this attempt
            remaining = num_traces - len(results)
            to_generate = max(1, int(remaining * generation_factor))

            print(f"\n=== Attempt {attempt}/{max_attempts} ===")
            print(f"Generating {to_generate} model traces (need {remaining} more)")

            # Generate batch
            batch_results = self.cluster.generate_batch(
                num_traces=to_generate,
                config=config,
                output_dir=output_dir,
                name_prefix=name_prefix,
                start_index=len(results)
            )

            # Keep only successful results, up to the needed amount
            successful = [r for r in batch_results if r.get('success', False)]
            to_add = min(len(successful), remaining)
            results.extend(successful[:to_add])

            print(f"Batch complete: {len(successful)} successful, {len(results)}/{num_traces} total")

        # Report final status
        if len(results) < num_traces:
            print(f"\nWarning: Only collected {len(results)}/{num_traces} traces after {attempt} attempts")
        else:
            print(f"\nSuccess: Generated {len(results)} traces")

        return results

    def generate_trace(self, config: Dict[str, Any], output_path: Path) -> Dict[str, Any]:
        """
        Generate a single runtime trace (backward compatibility).

        Args:
            config: Configuration parameters
            output_path: Path for output trace file

        Returns:
            Result dictionary with generation status
        """
        results = self.generate_traces(config, output_path.parent, output_path.stem)
        return results[0] if results else {
            "success": False,
            "error": "No traces generated"
        }

    def get_default_config(self) -> Dict[str, Any]:
        """
        Get default configuration for ZooKeeper trace generation.

        Returns:
            Dictionary with default parameters
        """
        return {
            "num_traces": 3,
            "generation_factor": 1.5,
            "max_attempts": 3,
            "simulation_depth": 100,
            "max_crashes": 2,
            "max_epoch": 3,
            "max_transactions": 2,
            "max_partitions": 0,
            "max_timeout_failures": 6
        }

    def get_available_scenarios(self) -> Dict[str, Dict[str, Any]]:
        """
        Get available predefined scenarios for ZooKeeper.

        Returns:
            Dictionary mapping scenario names to configurations
        """
        return {
            "normal_operation": {
                "description": "Normal operation without failures",
                "max_crashes": 0,
                "max_partitions": 0,
                "simulation_depth": 50,
                "max_epoch": 2
            },
            "with_failures": {
                "description": "Operation with node crashes and partitions",
                "max_crashes": 2,
                "max_partitions": 1,
                "simulation_depth": 100,
                "max_epoch": 3
            },
            "leader_election": {
                "description": "Focus on leader election scenarios",
                "max_crashes": 2,
                "max_partitions": 0,
                "simulation_depth": 30,
                "max_epoch": 3
            },
            "stress_test": {
                "description": "High complexity with many failures",
                "max_crashes": 3,
                "max_partitions": 2,
                "simulation_depth": 150,
                "max_epoch": 4,
                "max_transactions": 3
            }
        }


class ZooKeeperSystemModule(SystemModule):
    """Complete ZooKeeper system implementation."""

    def __init__(self, spec_path: str = None):
        """
        Initialize system module.

        Args:
            spec_path: Optional path to TLA+ specification for converter
        """
        self._trace_generator = ZooKeeperTraceGenerator()
        self._trace_converter = ZooKeeperTraceConverter(spec_path)
        self.spec_path = spec_path

    def get_trace_generator(self) -> TraceGenerator:
        """Get the ZooKeeper trace generator."""
        return self._trace_generator

    def get_trace_converter(self) -> TraceConverter:
        """Get the ZooKeeper trace converter."""
        return self._trace_converter

    def get_system_name(self) -> str:
        """Get the system name identifier."""
        return "zookeeper"


def get_system() -> SystemModule:
    """
    Factory function to get the ZooKeeper system implementation.

    This function is called by the system registry to load this system.

    Returns:
        ZooKeeperSystemModule instance
    """
    return ZooKeeperSystemModule()
