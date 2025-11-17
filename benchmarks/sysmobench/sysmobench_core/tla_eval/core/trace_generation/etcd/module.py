"""
ETCD system implementation for trace generation and conversion.

This module implements the system-specific interfaces for etcd raft
trace generation and format conversion.
"""

from pathlib import Path
from typing import Dict, Any, List
from datetime import datetime

from ..base import TraceGenerator, TraceConverter, SystemModule
from .cluster import RaftCluster, FileTraceLogger
from .event_driver import RandomEventDriver
from .trace_converter_impl import ETCDTraceConverterImpl


class ETCDTraceGenerator(TraceGenerator):
    """ETCD-specific trace generator implementation."""

    def generate_traces(self, config: Dict[str, Any], output_dir: Path, name_prefix: str = "trace") -> List[Dict[str, Any]]:
        """
        Generate multiple runtime traces using real etcd raft cluster.

        Args:
            config: Configuration for trace generation
            output_dir: Directory where trace files should be saved
            name_prefix: Prefix for trace file names

        Returns:
            List of dictionaries with generation results for each trace
        """
        # Get number of traces to generate (default to 1)
        num_traces = config.get('num_traces', 1)
        results = []

        for i in range(num_traces):
            # Generate output path for this trace
            trace_filename = f"{name_prefix}_{i+1:02d}.ndjson"
            output_path = output_dir / trace_filename

            # Generate single trace
            result = self.generate_trace(config, output_path)
            results.append(result)

            # Stop if a trace generation fails
            if not result.get('success', False):
                break

        return results

    def generate_trace(self, config: Dict[str, Any], output_path: Path) -> Dict[str, Any]:
        """
        Generate runtime trace using real etcd raft cluster.
        
        Args:
            config: Configuration for trace generation
            output_path: Path where trace file should be saved
            
        Returns:
            Dictionary with generation results
        """
        try:
            # Extract configuration parameters with defaults
            node_count = config.get("node_count", 3)
            duration = config.get("duration_seconds", 60)
            client_qps = config.get("client_qps", 10.0)
            fault_rate = config.get("fault_rate", 0.1)
            scenario = config.get("scenario", "normal_operation")
            
            print(f"Generating etcd trace: {node_count} nodes, {duration}s duration, {client_qps} QPS")
            
            # Initialize real etcd raft cluster
            trace_logger = FileTraceLogger(str(output_path))
            cluster = RaftCluster(node_count, trace_logger)
            
            # Initialize event driver with scenario
            driver = RandomEventDriver(cluster, config)
            driver.set_scenario(scenario)
            
            # Start cluster
            cluster.start()
            
            # Run trace generation
            start_time = datetime.now()
            trace_result = driver.run_scenario(duration)
            generation_duration = (datetime.now() - start_time).total_seconds()
            
            # Stop cluster and finalize trace
            cluster.stop()
            
            # Get event count from trace generation result, not from trace_logger
            if trace_result and trace_result.get("success", False):
                event_count = trace_result.get("event_count", 0)
                actual_trace_file = trace_result.get("trace_file", str(output_path))
            else:
                event_count = 0
                actual_trace_file = str(output_path)
            
            print(f"Generated {event_count} etcd events in {generation_duration:.2f}s")
            
            return {
                "success": True,
                "trace_file": actual_trace_file,
                "event_count": event_count,
                "duration": generation_duration,
                "metadata": {
                    "cluster_size": node_count,
                    "scenario": scenario,
                    "client_qps": client_qps,
                    "fault_rate": fault_rate
                }
            }
            
        except Exception as e:
            return {
                "success": False,
                "error": f"ETCD trace generation failed: {str(e)}"
            }
    
    def get_default_config(self) -> Dict[str, Any]:
        """Get default configuration for etcd trace generation."""
        return {
            "node_count": 3,
            "duration_seconds": 10,
            "client_qps": 5.0,
            "fault_rate": 0.1,
            "scenario": "normal_operation",
            "enable_network_faults": True,
            "enable_node_restart": True
        }
    
    def get_available_scenarios(self) -> Dict[str, Dict[str, Any]]:
        """Get available predefined scenarios for etcd."""
        # Create a dummy driver to get scenario configs
        dummy_cluster = None
        driver = RandomEventDriver(dummy_cluster, {})
        
        scenarios = {}
        scenario_names = ["normal_operation", "light_faults", "heavy_faults", 
                         "high_load", "partition_focused"]
        
        for name in scenario_names:
            scenarios[name] = driver.get_scenario_config(name)
            
        return scenarios


class ETCDTraceConverter(TraceConverter):
    """ETCD-specific trace converter implementation."""

    def __init__(self, spec_path: str = None):
        """Initialize converter with optional spec path for mapping files."""
        self.spec_path = spec_path

    def convert_trace(self, input_path: Path, output_path: Path, spec_path: Path = None) -> Dict[str, Any]:
        """
        Convert etcd system trace to TLA+ specification-compatible format.
        
        Args:
            input_path: Path to the raw etcd trace file
            output_path: Path where converted trace should be saved
            
        Returns:
            Dictionary with conversion results
        """
        try:
            print(f"Converting etcd trace from {input_path} to {output_path}")

            # Use spec_path if provided, otherwise use instance spec_path
            effective_spec_path = str(spec_path) if spec_path else self.spec_path

            # Initialize etcd trace converter with spec path
            converter = ETCDTraceConverterImpl(spec_path=effective_spec_path)
            
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
                "error": f"ETCD trace conversion failed: {str(e)}"
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
        return ETCDTraceConverterImpl.generate_mapping_with_llm(
            spec_file=str(spec_file),
            model_name=model_name,
            output_path=str(output_path) if output_path else None
        )


class ETCDSystemModule(SystemModule):
    """Complete ETCD system implementation."""

    def __init__(self, spec_path: str = None):
        self._trace_generator = ETCDTraceGenerator()
        self._trace_converter = ETCDTraceConverter(spec_path=spec_path)
        self.spec_path = spec_path
    
    def get_trace_generator(self) -> TraceGenerator:
        """Get the etcd trace generator."""
        return self._trace_generator
    
    def get_trace_converter(self) -> TraceConverter:
        """Get the etcd trace converter."""
        return self._trace_converter
    
    def get_system_name(self) -> str:
        """Get the system name identifier."""
        return "etcd"


def get_system() -> SystemModule:
    """
    Factory function to get the ETCD system implementation.
    
    This function is called by the system registry to load this system.
    
    Returns:
        ETCDSystemModule instance
    """
    return ETCDSystemModule()