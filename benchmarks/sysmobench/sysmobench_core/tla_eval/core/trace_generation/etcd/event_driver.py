"""
Random event driver for etcd raft cluster operations.

This module coordinates with the Go-based trace generator to create
realistic operational scenarios with client requests and fault injection.
"""

from typing import Dict, Any
import time


class RandomEventDriver:
    """
    Coordinates random events for raft cluster trace generation.
    
    This driver works with the RaftCluster to generate realistic
    operational scenarios including client requests, fault injection,
    and network partitions.
    """
    
    def __init__(self, cluster: 'RaftCluster', config: Dict[str, Any]):
        """
        Initialize random event driver.
        
        Args:
            cluster: RaftCluster instance to drive
            config: Configuration for event generation
        """
        self.cluster = cluster
        self.config = config
        
        # Extract configuration parameters
        self.client_qps = config.get("client_qps", 10.0)
        self.fault_rate = config.get("fault_rate", 0.1)
        self.enable_network_faults = config.get("enable_network_faults", True)
        self.enable_node_restart = config.get("enable_node_restart", True)
        
    def run_for_duration(self, duration_seconds: int) -> Dict[str, Any]:
        """
        Run random operations for the specified duration.
        
        Args:
            duration_seconds: How long to run operations
            
        Returns:
            Dictionary with operation results
        """
        print(f"Starting random event driver for {duration_seconds} seconds...")
        print(f"Client QPS: {self.client_qps}, Fault rate: {self.fault_rate}")
        
        # The actual work is done by the Go trace generator
        # This Python driver just coordinates the overall process
        filter_type = self.config.get("filter_type", "coarse")
        result = self.cluster.generate_trace(
            duration_seconds=duration_seconds,
            client_qps=self.client_qps,
            fault_rate=self.fault_rate,
            filter_type=filter_type
        )
        
        if result["success"]:
            print(f"Event driver completed successfully:")
            print(f"  - Generated {result['event_count']} trace events")
            print(f"  - Duration: {result['duration']:.2f} seconds")
            print(f"  - Trace file: {result['trace_file']}")
        else:
            print(f"Event driver failed: {result.get('error', 'Unknown error')}")
            
        return result
    
    def get_scenario_config(self, scenario: str) -> Dict[str, Any]:
        """
        Get predefined configuration for common scenarios.
        
        Args:
            scenario: Name of the scenario
            
        Returns:
            Configuration dictionary for the scenario
        """
        scenarios = {
            "normal_operation": {
                "client_qps": 10.0,
                "fault_rate": 0.0,
                "enable_network_faults": False,
                "enable_node_restart": False
            },
            "light_faults": {
                "client_qps": 10.0,
                "fault_rate": 0.05,
                "enable_network_faults": True,
                "enable_node_restart": False
            },
            "heavy_faults": {
                "client_qps": 15.0,
                "fault_rate": 0.2,
                "enable_network_faults": True,
                "enable_node_restart": True
            },
            "high_load": {
                "client_qps": 50.0,
                "fault_rate": 0.1,
                "enable_network_faults": True,
                "enable_node_restart": False
            },
            "partition_focused": {
                "client_qps": 5.0,
                "fault_rate": 0.3,
                "enable_network_faults": True,
                "enable_node_restart": False
            }
        }
        
        return scenarios.get(scenario, scenarios["normal_operation"])
    
    def set_scenario(self, scenario: str):
        """
        Set the scenario configuration for the event driver.
        
        Args:
            scenario: Name of the scenario to use
        """
        scenario_config = self.get_scenario_config(scenario)
        self.config.update(scenario_config)
        
        # Update instance variables
        self.client_qps = self.config.get("client_qps", 10.0)
        self.fault_rate = self.config.get("fault_rate", 0.1)
        self.enable_network_faults = self.config.get("enable_network_faults", True)
        self.enable_node_restart = self.config.get("enable_node_restart", True)
        
        print(f"Set scenario '{scenario}' with config: {scenario_config}")
    
    def run_scenario(self, duration_seconds: int) -> Dict[str, Any]:
        """
        Run the configured scenario for the specified duration.
        
        Args:
            duration_seconds: How long to run the scenario
            
        Returns:
            Dictionary with operation results
        """
        return self.run_for_duration(duration_seconds)