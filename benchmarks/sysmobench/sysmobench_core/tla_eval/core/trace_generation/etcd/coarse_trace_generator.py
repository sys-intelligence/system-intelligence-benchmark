"""
Coarse-grained trace generator for etcd specifications.

This module generates abstract, high-level traces that focus on
key raft operations (election and log synchronization) that can be
validated across different TLA+ specifications with varying granularity.
"""

import json
import time
from typing import List, Dict, Any, Optional
from dataclasses import dataclass
import random


@dataclass
class CoarseTraceEvent:
    """Represents a high-level raft operation."""
    timestamp: float
    event_type: str  # "Election" or "LogSync"
    leader: int
    term: int
    participants: List[int]
    log_index: Optional[int] = None
    success: bool = True
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for JSON serialization."""
        return {
            "timestamp": self.timestamp,
            "event": self.event_type,
            "leader": self.leader,
            "term": self.term,
            "participants": self.participants,
            "log_index": self.log_index,
            "success": self.success
        }


class CoarseTraceGenerator:
    """
    Generates coarse-grained traces focusing on high-level raft operations.
    
    This generator creates abstract traces that capture the essential
    raft behaviors without fine-grained implementation details.
    """
    
    def __init__(self, node_count: int = 3, seed: Optional[int] = None):
        """
        Initialize coarse trace generator.
        
        Args:
            node_count: Number of nodes in the cluster
            seed: Random seed for reproducible traces
        """
        self.node_count = node_count
        self.nodes = list(range(1, node_count + 1))
        self.current_term = 1
        self.current_leader = None
        self.log_index = 0
        
        if seed is not None:
            random.seed(seed)
        
        self.events: List[CoarseTraceEvent] = []
    
    def generate_election(self, forced_leader: Optional[int] = None) -> CoarseTraceEvent:
        """
        Generate an election event.
        
        Args:
            forced_leader: Force specific node to become leader (for testing)
            
        Returns:
            Election event
        """
        # Choose new leader (different from current if possible)
        candidates = [n for n in self.nodes if n != self.current_leader]
        if not candidates:
            candidates = self.nodes
            
        new_leader = forced_leader if forced_leader else random.choice(candidates)
        
        # Election typically involves majority of nodes
        participants = random.sample(
            self.nodes, 
            min(len(self.nodes), random.randint(len(self.nodes)//2 + 1, len(self.nodes)))
        )
        
        # Elections usually increment term
        if new_leader != self.current_leader:
            self.current_term += 1
        
        event = CoarseTraceEvent(
            timestamp=time.time(),
            event_type="Election",
            leader=new_leader,
            term=self.current_term,
            participants=participants,
            success=True
        )
        
        self.current_leader = new_leader
        self.events.append(event)
        return event
    
    def generate_log_sync(self, entry_count: int = 1) -> CoarseTraceEvent:
        """
        Generate a log synchronization event.
        
        Args:
            entry_count: Number of log entries to sync
            
        Returns:
            Log sync event
        """
        if self.current_leader is None:
            # Need a leader first
            self.generate_election()
        
        # Log sync involves leader and followers
        participants = [self.current_leader] + [
            n for n in self.nodes if n != self.current_leader
        ]
        
        # Advance log index
        old_index = self.log_index
        self.log_index += entry_count
        
        event = CoarseTraceEvent(
            timestamp=time.time(),
            event_type="LogSync",
            leader=self.current_leader,
            term=self.current_term,
            participants=participants,
            log_index=self.log_index,
            success=True
        )
        
        self.events.append(event)
        return event
    
    def generate_scenario(self, scenario_name: str = "basic") -> List[CoarseTraceEvent]:
        """
        Generate a predefined scenario.
        
        Args:
            scenario_name: Name of scenario to generate
            
        Returns:
            List of generated events
        """
        scenarios = {
            "basic": self._basic_scenario,
            "leader_change": self._leader_change_scenario,
            "frequent_elections": self._frequent_elections_scenario,
            "log_heavy": self._log_heavy_scenario
        }
        
        if scenario_name not in scenarios:
            scenario_name = "basic"
            
        return scenarios[scenario_name]()
    
    def _basic_scenario(self) -> List[CoarseTraceEvent]:
        """Basic scenario: election + several log syncs."""
        events = []
        
        # Initial election
        events.append(self.generate_election())
        time.sleep(0.1)  # Small delay for timestamp
        
        # Several log synchronizations
        for _ in range(5):
            events.append(self.generate_log_sync())
            time.sleep(0.1)
            
        return events
    
    def _leader_change_scenario(self) -> List[CoarseTraceEvent]:
        """Scenario with leader changes."""
        events = []
        
        # Initial election and some log syncs
        events.append(self.generate_election())
        time.sleep(0.1)
        
        for _ in range(3):
            events.append(self.generate_log_sync())
            time.sleep(0.1)
        
        # Leader change
        events.append(self.generate_election())
        time.sleep(0.1)
        
        # More log syncs with new leader
        for _ in range(3):
            events.append(self.generate_log_sync())
            time.sleep(0.1)
            
        return events
    
    def _frequent_elections_scenario(self) -> List[CoarseTraceEvent]:
        """Scenario with frequent elections (unstable network)."""
        events = []
        
        for _ in range(4):
            events.append(self.generate_election())
            time.sleep(0.1)
            # Few log syncs between elections
            for _ in range(2):
                events.append(self.generate_log_sync())
                time.sleep(0.1)
            
        return events
    
    def _log_heavy_scenario(self) -> List[CoarseTraceEvent]:
        """Scenario with heavy log synchronization."""
        events = []
        
        # Initial election
        events.append(self.generate_election())
        time.sleep(0.1)
        
        # Many log syncs
        for _ in range(10):
            entry_count = random.randint(1, 3)
            events.append(self.generate_log_sync(entry_count))
            time.sleep(0.1)
            
        return events
    
    def save_trace(self, output_file: str, scenario: str = "basic") -> Dict[str, Any]:
        """
        Generate and save a coarse trace to file.
        
        Args:
            output_file: Path to save trace file
            scenario: Scenario name to generate
            
        Returns:
            Generation results
        """
        try:
            # Generate scenario
            events = self.generate_scenario(scenario)
            
            # Prepare trace data
            trace_data = {
                "metadata": {
                    "generator": "CoarseTraceGenerator",
                    "node_count": self.node_count,
                    "scenario": scenario,
                    "event_count": len(events),
                    "generated_at": time.time()
                },
                "events": [event.to_dict() for event in events]
            }
            
            # Save to file
            with open(output_file, 'w') as f:
                json.dump(trace_data, f, indent=2)
            
            return {
                "success": True,
                "trace_file": output_file,
                "event_count": len(events),
                "scenario": scenario
            }
            
        except Exception as e:
            return {
                "success": False,
                "error": str(e)
            }
    
    def get_state_summary(self) -> Dict[str, Any]:
        """Get current cluster state summary."""
        return {
            "current_term": self.current_term,
            "current_leader": self.current_leader,
            "log_index": self.log_index,
            "total_events": len(self.events)
        }


def generate_coarse_trace(output_file: str, 
                         scenario: str = "basic",
                         node_count: int = 3,
                         seed: Optional[int] = None) -> Dict[str, Any]:
    """
    Convenience function to generate a coarse trace.
    
    Args:
        output_file: Path to save trace file
        scenario: Scenario name ("basic", "leader_change", "frequent_elections", "log_heavy")
        node_count: Number of nodes in cluster
        seed: Random seed for reproducible traces
        
    Returns:
        Generation results
    """
    generator = CoarseTraceGenerator(node_count=node_count, seed=seed)
    return generator.save_trace(output_file, scenario)


# Command line interface
if __name__ == "__main__":
    import argparse
    
    parser = argparse.ArgumentParser(description="Generate coarse-grained raft traces")
    parser.add_argument("--output", "-o", required=True, help="Output trace file")
    parser.add_argument("--scenario", "-s", default="basic", 
                       choices=["basic", "leader_change", "frequent_elections", "log_heavy"],
                       help="Scenario to generate")
    parser.add_argument("--nodes", "-n", type=int, default=3, help="Number of nodes")
    parser.add_argument("--seed", type=int, default=None, help="Random seed")
    
    args = parser.parse_args()
    
    print(f"Generating coarse trace: {args.scenario}")
    result = generate_coarse_trace(
        args.output, 
        args.scenario, 
        args.nodes, 
        args.seed
    )
    
    if result["success"]:
        print(f"✅ Trace generated successfully:")
        print(f"   File: {result['trace_file']}")
        print(f"   Events: {result['event_count']}")
        print(f"   Scenario: {result['scenario']}")
    else:
        print(f"❌ Failed to generate trace: {result['error']}")