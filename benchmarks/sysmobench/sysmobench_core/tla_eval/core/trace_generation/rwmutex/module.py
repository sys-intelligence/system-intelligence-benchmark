"""
Asterinas RwMutex system implementation for trace generation and conversion.

This module implements the system-specific interfaces for Asterinas RwMutex
trace generation and format conversion using REAL kernel tests in Docker containers.
"""

import subprocess
import json
import tempfile
import shutil
import os
import time
import re
from pathlib import Path
from typing import Dict, Any, List
from datetime import datetime

from ..base import TraceGenerator, TraceConverter, SystemModule


class RwMutexTraceGenerator(TraceGenerator):
    """Asterinas RwMutex-specific REAL-TIME trace generator implementation using Docker."""
    
    def __init__(self):
        self.docker_image = "asterinas/asterinas:0.16.0-20250822"
        self.workspace_path = "/workspace"
        self.timeout_seconds = 600  # 10 minutes for full build + test process (100 traces)
        self._cached_traces = {}  
    
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
            test_name = config.get("test_name", "test_rwmutex_trace")
            # Use num_traces if provided (from trace_validation), otherwise fall back to num_runs
            # For test_rwmutex_trace, default to 100 traces
            if test_name == "test_rwmutex_trace":
                num_runs = config.get("num_traces", config.get("num_runs", 100))
            else:
                num_runs = config.get("num_traces", config.get("num_runs", 1))
            scenario_type = config.get("scenario_type", "real_kernel_test")
            
            print(f"Generating REAL RwMutex traces using Asterinas kernel test: {test_name}")
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
            
            # Setup Asterinas repository if needed
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
            
            # Special handling for test_rwmutex_trace which generates 20 traces in one run
            if test_name == "test_rwmutex_trace":
                print(f"Special handling for test_rwmutex_trace: will generate 100 traces in one Docker run")
                
                # Check if we have cached traces for this test
                cache_key = f"{test_name}_{asterinas_path}"

                # Clear cache to force fresh run with fixed kernel code
                print(f"Clearing all cached traces to use fixed kernel code")
                self._cached_traces.clear()

                if cache_key not in self._cached_traces:
                    # Run the test once to get all 100 traces (5 batches of 20)
                    print(f"Running kernel test to generate 100 traces...")
                    
                    # Run kernel test and parse all traces
                    all_traces = self._run_and_parse_all_traces(
                        asterinas_path,
                        test_name
                    )
                    
                    if not all_traces:
                        # If failed, return error for all traces
                        for i in range(num_runs):
                            trace_results.append({
                                "success": False,
                                "error": "Failed to generate traces from kernel test",
                                "trace_file": "",
                                "event_count": 0,
                                "duration": 0.0,
                                "metadata": {"run_id": i, "failed": True}
                            })
                        return trace_results
                    
                    # Cache the parsed traces
                    self._cached_traces[cache_key] = all_traces
                    print(f"Cached {len(all_traces)} traces from kernel test")
                else:
                    print(f"Using cached traces from previous run")
                    all_traces = self._cached_traces[cache_key]
                
                # Now save individual trace files
                for run_id in range(min(num_runs, len(all_traces))):
                    output_path = output_dir / f"trace_{run_id+1:02d}.jsonl"
                    
                    trace_events = all_traces[run_id]
                    
                    # Save this specific trace to file
                    with open(output_path, 'w') as f:
                        f.write(f"# TRACE_{run_id + 1}: RwMutex Single Lock, 3-Thread Mixed Read/Write\n")
                        f.write(f"# Generated from test_rwmutex_trace, Timestamp: {datetime.now().isoformat()}\n")
                        for event in trace_events:
                            f.write(json.dumps(event) + '\n')
                    
                    result = {
                        "success": True,
                        "trace_file": str(output_path),
                        "event_count": len(trace_events),
                        "duration": 0.5,  # Approximate time per trace
                        "metadata": {
                            "sync_primitive": "rwmutex",
                            "source": "asterinas_kernel_real",
                            "test_name": test_name,
                            "generation_mode": scenario_type,
                            "docker_image": self.docker_image,
                            "run_id": run_id,
                            "trace_index": run_id + 1
                        }
                    }
                    
                    print(f"Successfully saved trace {run_id + 1}/{num_runs} with {len(trace_events)} events")
                    trace_results.append(result)
            
            else:
                # Regular handling for other tests
                for run_id in range(num_runs):
                    print(f"Running kernel test {run_id + 1}/{num_runs}...")
                    
                    # Create output path for this run
                    output_path = output_dir / f"trace_{run_id+1:02d}.jsonl"
                    
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
                            "sync_primitive": "rwmutex",
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
                "error": f"Real RwMutex trace generation failed: {str(e)}",
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
            if not (asterinas_path / "ostd").exists():
                print(f"Invalid Asterinas repository structure at {asterinas_path}")
                return None
                
            print(f"Using Asterinas repository at {asterinas_path}")
            return asterinas_path
            
        except Exception as e:
            print(f"Failed to prepare Asterinas repository: {e}")
            return None
    
    def _run_and_parse_all_traces(self, asterinas_path: Path, test_name: str) -> List[List[Dict[str, Any]]]:
        """Run kernel test once and parse all traces from the output."""
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
                cd ostd &&
                rm -rf target/ &&
                cargo clean &&
                timeout {self.timeout_seconds} cargo osdk test --features tla-trace --target-arch x86_64 --qemu-args="-accel tcg" {test_name} 2>&1
                """
            ]
            
            print(f"Running Docker command for kernel test {test_name}...")
            
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
            
            # Parse and split traces from output
            all_traces = self._parse_and_split_traces(result.stdout)
            
            if not all_traces:
                print("No traces parsed from kernel output")
                return []
            
            print(f"Successfully parsed {len(all_traces)} traces from kernel output")
            return all_traces
            
        except subprocess.TimeoutExpired:
            print(f"Kernel test {test_name} timed out")
            return []
        except Exception as e:
            print(f"Failed to run kernel test: {e}")
            return []
    
    def _run_real_kernel_test(self, asterinas_path: Path, test_name: str, output_path: Path, run_id: int) -> Dict[str, Any]:
        """Run real Asterinas kernel test in Docker container and extract traces."""
        try:
            # Use the provided output_path directly
            run_output_path = output_path
            
            # Build Docker run command - non-interactive mode for automation
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
                cd ostd &&
                rm -rf target/ &&
                cargo clean &&
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
                timeout=self.timeout_seconds + 120  # Add buffer for Docker overhead (build takes time)
            )
            execution_time = time.time() - start_time
            
            print(f"Docker execution completed in {execution_time:.2f}s")
            print(f"Return code: {result.returncode}")
            
            # Print ALL output - no truncation
            print(f"\n=== FULL STDOUT ===")
            print(result.stdout)
            print(f"\n=== FULL STDERR ===")  
            print(result.stderr)
            print(f"=== END OUTPUT ===\n")
            
            # Extract and split trace events from the output
            all_traces = self._parse_and_split_traces(result.stdout)
            
            if not all_traces:
                print("No trace events found in output")
                return {
                    "success": False,
                    "error": f"No trace events extracted from kernel test {test_name}",
                    "execution_time": execution_time
                }
            
            # For test_rwmutex_trace which generates multiple traces, we'll save them separately
            # Otherwise save as a single trace
            if test_name == "test_rwmutex_trace" and len(all_traces) > 0:
                # Return info about the trace (this will be called multiple times with different run_id)
                trace_index = run_id % len(all_traces)
                if trace_index < len(all_traces):
                    trace_events = all_traces[trace_index]
                    
                    # Save this specific trace to file
                    with open(run_output_path, 'w') as f:
                        f.write(f"# TRACE_{trace_index + 1}: RwMutex Single Lock, 3-Thread Mixed Read/Write\n")
                        f.write(f"# Run ID: {run_id}, Timestamp: {datetime.now().isoformat()}\n")
                        for event in trace_events:
                            f.write(json.dumps(event) + '\n')
                    
                    print(f"Saved trace {trace_index + 1} with {len(trace_events)} events to {run_output_path}")
                    
                    return {
                        "success": True,
                        "trace_file": str(run_output_path),
                        "event_count": len(trace_events),
                        "execution_time": execution_time,
                        "test_name": test_name,
                        "run_id": run_id,
                        "trace_index": trace_index + 1
                    }
            else:
                # For other tests, save all events as a single trace
                trace_events = [event for trace in all_traces for event in trace]
                
                with open(run_output_path, 'w') as f:
                    f.write(f"# Real-time RwMutex trace from Asterinas kernel test: {test_name}\n")
                    f.write(f"# Run ID: {run_id}, Timestamp: {datetime.now().isoformat()}\n")
                    for event in trace_events:
                        f.write(json.dumps(event) + '\n')
                
                print(f"Saved {len(trace_events)} trace events to {run_output_path}")
                
                return {
                    "success": True,
                    "trace_file": str(run_output_path),
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
    
    def _parse_and_split_traces(self, output: str) -> List[List[Dict[str, Any]]]:
        """Parse and split multiple traces from Asterinas kernel test output."""
        all_traces = []
        current_trace = []

        print(f"Parsing and splitting output of {len(output)} characters")

        lines = output.split('\n')
        print(f"Processing {len(lines)} lines")

        # Count trace markers first
        trace_markers = [line for line in lines if '--- TRACE' in line]
        print(f"Found {len(trace_markers)} trace markers total")

        import re
        json_pattern = r'\{"seq":\d+,"thread":\d+,"rwmutex":\d+,"state":"[^"]*","lock_type":"[^"]*","action":"[^"]*","actor":\d+\}'

        for line_num, line in enumerate(lines):
            line = line.strip()

            # Look for trace markers - when we find one, save the previous trace
            if '--- TRACE' in line:
                if current_trace:
                    all_traces.append(current_trace)
                    print(f"Saved trace {len(all_traces)} with {len(current_trace)} events")
                current_trace = []
                continue

            # Skip empty lines and non-JSON lines
            if not line or '{' not in line:
                continue

            # Try to extract JSON events from the line
            matches = re.findall(json_pattern, line)

            # If exact pattern doesn't match, try more flexible patterns
            if not matches:
                flexible_pattern = r'\{[^}]*"seq":\d+[^}]*"action":"[^"]*"[^}]*\}'
                matches = re.findall(flexible_pattern, line)

            # Process all JSON matches found in this line
            for match in matches:
                try:
                    event = json.loads(match)
                    if 'seq' in event and 'action' in event:
                        if 'actor' not in event and 'thread' in event:
                            event['actor'] = event['thread']
                        current_trace.append(event)
                except json.JSONDecodeError:
                    continue

            # Handle concatenated JSON (like }{"seq":...)
            if '}{' in line:
                for part in line.split('}{'):
                    if not part.startswith('{'):
                        part = '{' + part
                    if not part.endswith('}'):
                        part = part + '}'
                    try:
                        event = json.loads(part)
                        if 'seq' in event and 'action' in event:
                            if 'actor' not in event and 'thread' in event:
                                event['actor'] = event['thread']
                            current_trace.append(event)
                    except json.JSONDecodeError:
                        continue

        # Don't forget the last trace
        if current_trace:
            all_traces.append(current_trace)
            print(f"Saved final trace {len(all_traces)} with {len(current_trace)} events")

        print(f"Successfully parsed {len(all_traces)} separate traces")

        # If we didn't get the expected number of traces, try sequence reset splitting
        if len(all_traces) != 100 and len(all_traces) > 0:
            print(f"Expected 100 traces but got {len(all_traces)}, trying sequence reset splitting...")
            if len(all_traces) == 1 and len(all_traces[0]) > 100:
                # All events might be in one trace, split by sequence resets
                all_traces = self._split_by_sequence_resets(all_traces[0])
                print(f"After sequence reset splitting: {len(all_traces)} traces")
        return all_traces
    
    def _split_by_sequence_resets(self, events: List[Dict[str, Any]]) -> List[List[Dict[str, Any]]]:
        """Split a list of events into multiple traces based on sequence number resets."""
        traces = []
        current_trace = []
        last_seq = -1
        
        for event in events:
            seq = event.get('seq', 0)
            
            # Detect sequence reset (seq goes back to 0 or a small number after a larger one)
            if seq < last_seq and last_seq > 10:  # Allow for some tolerance
                if current_trace:
                    traces.append(current_trace)
                current_trace = [event]
            else:
                current_trace.append(event)
            
            last_seq = seq
        
        # Add the last trace
        if current_trace:
            traces.append(current_trace)
        
        # If we got exactly 100 traces, it's likely the test_rwmutex_trace output
        if len(traces) == 100:
            print(f"Successfully split into 100 traces by sequence resets")
        
        return traces
    
    def get_default_config(self) -> Dict[str, Any]:
        """Get default configuration for REAL RwMutex trace generation."""
        return {
            "test_name": "test_rwmutex_trace",
            "num_runs": 100,
            "scenario_type": "real_kernel_test",
            "source": "asterinas_kernel_real",
            "enable_tla_trace": True,
            "timeout_seconds": 600
        }
    
    def get_available_scenarios(self) -> Dict[str, Dict[str, Any]]:
        """Get available real kernel test scenarios for RwMutex testing."""
        return {
            "rwmutex_trace_100": {
                "test_name": "test_rwmutex_trace",
                "num_runs": 100,
                "scenario_type": "real_kernel_test",
                "description": "Generate 100 different RwMutex trace scenarios with read/write operations"
            },
            "rwmutex_dedicated": {
                "test_name": "test_rwmutex_tla_trace",
                "num_runs": 1,
                "scenario_type": "real_kernel_test",
                "description": "Dedicated RwMutex test with complex locking patterns"
            },
            "simple_test": {
                "test_name": "test_tla_trace_simple",
                "num_runs": 1,
                "scenario_type": "real_kernel_test",
                "description": "Simple RwMutex randomized operations test"
            },
            "multiple_runs": {
                "test_name": "test_rwmutex_trace",
                "num_runs": 3,
                "scenario_type": "real_kernel_test",
                "description": "Multiple runs of 20-scenario test for consistency"
            },
            "stress_test": {
                "test_name": "test_rwmutex_trace",
                "num_runs": 5,
                "scenario_type": "real_kernel_test",
                "description": "Stress testing with multiple kernel runs"
            }
        }


class RwMutexTraceConverter(TraceConverter):
    """RwMutex-specific trace converter implementation using configuration-based approach."""
    
    def __init__(self):
        from .trace_converter_impl import RwMutexTraceConverterImpl
        self.impl = RwMutexTraceConverterImpl()
    
    def convert_trace(self, input_path: Path, output_path: Path) -> Dict[str, Any]:
        """
        Convert RwMutex trace to TLA+ specification-compatible format.
        
        Args:
            input_path: Path to the raw RwMutex trace file
            output_path: Path where converted trace should be saved
            
        Returns:
            Dictionary with conversion results
        """
        return self.impl.convert_trace(str(input_path), str(output_path))


class RwMutexSystemModule(SystemModule):
    """Complete RwMutex system implementation."""
    
    def __init__(self):
        self._trace_generator = RwMutexTraceGenerator()
        self._trace_converter = RwMutexTraceConverter()
    
    def get_trace_generator(self) -> TraceGenerator:
        """Get the RwMutex trace generator."""
        return self._trace_generator
    
    def get_trace_converter(self) -> TraceConverter:
        """Get the RwMutex trace converter."""
        return self._trace_converter
    
    def get_system_name(self) -> str:
        """Get the system name identifier."""
        return "rwmutex"


def get_system() -> SystemModule:
    """
    Factory function to get the RwMutex system implementation.
    
    This function is called by the system registry to load this system.
    
    Returns:
        RwMutexSystemModule instance
    """
    return RwMutexSystemModule()