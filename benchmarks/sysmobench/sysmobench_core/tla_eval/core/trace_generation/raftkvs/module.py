"""
RaftKVS system implementation for trace generation and conversion.
"""

from ..base import TraceGenerator, TraceConverter, SystemModule

import subprocess
from pathlib import Path
from typing import Dict, Any
from datetime import datetime

class RaftKVSTraceGenerator(TraceGenerator):
    def generate_traces(self, config: Dict[str, Any], output_path: Path) -> Dict[str, Any]:
        """
        Generate runtime trace using real etcd raft cluster.
        
        Args:
            config: Configuration for trace generation
            output_path: Path where trace file should be saved
            
        Returns:
            Dictionary with generation results
        """
        try:
            scenario = config["scenario"]
            server_count = config["server_count"]
            
            print(f"Generating raftkvs trace: {scenario}, which has {server_count} servers")

            start_time = datetime.now()

            subprocess.run(
                ["go", "test", "-run", scenario],
                check=True,
                env={
                    "PGO_TRACE_DIR": output_path,
                    "PGO_DISRUPT_CONCURRENCY": "100us",
                },
                capture_output=True,
            )

            generation_duration = (datetime.now() - start_time).total_seconds()
            
            print(f"Generated raftkvs trace in {generation_duration:.2f}s")
            
            return {
                "success": True,
                "trace_folder": output_path,
                "duration": generation_duration,
                "metadata": config,
            }
            
        except Exception as e:
            return {
                "success": False,
                "error": f"Raftkvs trace generation failed: {str(e)}"
            }
    
    def get_default_config(self) -> Dict[str, Any]:
        return self.get_available_scenarios()[0]
    
    def get_available_scenarios(self) -> Dict[str, Dict[str, Any]]:
        return [
            {
                "scenario": "TestSafety_OneServer",
                "server_count": 1,
            },
            {
                "scenario": "TestSafety_TwoServers",
                "server_count": 2,
            },
            {
                "scenario": "TestSafety_ThreeServers",
                "server_count": 3,
            },
            {
                "scenario": "TestSafety_FourServers",
                "server_count": 4,
            },
            {
                "scenario": "TestSafety_FiveServers",
                "server_count": 5,
            },
            {
                "scenario": "TestSafety_OneFailing_ThreeServers",
                "server_count": 3,
            },
        ]

class RaftKVSTraceConverter(TraceConverter):
    def __init__(self):
        self._sys_root = Path(__file__).parents[0]
        self._pgo_jar = self._sys_root / "pgo.jar"

    def convert_trace(self, input_path: Path, output_path: Path) -> Dict[str, Any]:
        try:
            print(f"Converting etcd trace from {input_path} to {output_path}")

            # FIXME: the "1" below is from the config by the generator

            subprocess.run(
                [self._pgo_jar, "tracegen", "--noall-paths", "--cfg-fragment-suffix", "1", "--logs-dir", input_path, self._sys_root / "raftkvs.tla", output_path],
                check=True,
                capture_output=True,
            )
            
            return {
                "success": True,
                "output_file": output_path / "raftkvsValidate.tla",
            }
                
        except Exception as e:
            return {
                "success": False,
                "error": f"Raftkvs trace conversion failed: {str(e)}"
            }

class RaftKVSSystemModule(SystemModule):
    def __init__(self):
        self._trace_generator = RaftKVSTraceGenerator()
        self._trace_converter = RaftKVSTraceConverter()
    
    def get_trace_generator(self) -> TraceGenerator:
        return self._trace_generator
    
    def get_trace_converter(self) -> TraceConverter:
        return self._trace_converter
    
    def get_system_name(self) -> str:
        return "raftkvs"

def get_system() -> SystemModule:
    """
    Factory function to get the RaftKVS system implementation.
    
    This function is called by the system registry to load this system.
    
    Returns:
        RaftKVSSystemModule instance
    """
    return RaftKVSSystemModule()
