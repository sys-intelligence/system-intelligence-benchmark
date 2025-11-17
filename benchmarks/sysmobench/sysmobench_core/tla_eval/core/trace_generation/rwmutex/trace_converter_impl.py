"""
RwMutex Trace Converter Implementation

State-tracker based implementation for RwMutex trace conversion.
Converts system traces to TLA+ trace validation format using complete state tracking.
"""

import json
import os
import subprocess
from typing import Dict, Any, List, Optional, Set, Tuple
from pathlib import Path
from .state_tracker import RwMutexStateTracker
from .universal_state_tracker import UniversalRwMutexStateTracker


class RwMutexTraceConverterImpl:
    """
    State-tracker based implementation for RwMutex trace conversion.

    This handles the conversion from raw RwMutex traces (JSONL format)
    to the format expected by TLA+ specifications for validation.
    """

    def __init__(self, mapping_file: str = None, auto_update_tla_config: bool = True, use_universal: bool = True):
        """
        Initialize trace converter with mapping configuration.

        Args:
            mapping_file: Path to JSON mapping file
            auto_update_tla_config: Whether to automatically update TLA+ config files
            use_universal: Whether to use universal state tracker
        """
        if mapping_file is None:
            # Look in data/convertor/rwmutex first, fallback to module directory
            data_mapping = "data/convertor/rwmutex/rwmutex_mapping.json"
            module_mapping = os.path.join(os.path.dirname(__file__), "rwmutex_mapping.json")

            if os.path.exists(data_mapping):
                mapping_file = data_mapping
            else:
                mapping_file = module_mapping

        self.mapping_file = mapping_file
        self.mapping = self._load_mapping()
        self.auto_update_tla_config = auto_update_tla_config
        self.use_universal = use_universal
        self.project_root = Path(__file__).parent.parent.parent.parent.parent

    def _load_mapping(self) -> Dict[str, Any]:
        """Load mapping configuration from JSON file."""
        try:
            with open(self.mapping_file, 'r') as f:
                mapping = json.load(f)
                print(f"Loaded RwMutex mapping configuration from: {self.mapping_file}")
                return mapping
        except Exception as e:
            print(f"Error loading mapping from {self.mapping_file}: {e}")
            # Return default mapping if file not found
            return self._get_default_mapping()

    def _get_default_mapping(self) -> Dict[str, Any]:
        """Get default mapping configuration if file not found."""
        return {
            "config": {
                "Threads": ["Thread0", "Thread1", "Thread2", "Thread3"]
            }
        }

    def convert_trace(self, input_file: str, output_file: str) -> Dict[str, Any]:
        """
        Convert raw rwmutex trace to TLA+ format.

        Args:
            input_file: Path to input JSONL trace file
            output_file: Path to output NDJSON trace file

        Returns:
            Dictionary with conversion results
        """
        try:
            print(f"Converting rwmutex trace: {input_file} -> {output_file}")

            # Read and parse input trace
            input_events = self._read_input_trace(input_file)
            if not input_events:
                return {
                    "success": False,
                    "error": "No events found in input trace",
                    "input_file": input_file,
                    "output_file": output_file,
                    "input_events": 0,
                    "output_transitions": 0
                }

            # Convert events to TLA+ format using state tracker
            output_transitions = self._convert_events(input_events)

            # Write output trace
            self._write_output_trace(output_transitions, output_file)

            print(f"Conversion successful: {len(input_events)} input events -> {len(output_transitions)} output transitions")

            return {
                "success": True,
                "input_file": input_file,
                "output_file": output_file,
                "input_events": len(input_events),
                "output_transitions": len(output_transitions)
            }

        except Exception as e:
            error_msg = f"Error converting trace {input_file}: {str(e)}"
            print(error_msg)
            return {
                "success": False,
                "error": error_msg,
                "input_file": input_file,
                "output_file": output_file,
                "input_events": 0,
                "output_transitions": 0
            }

    def _read_input_trace(self, input_file: str) -> List[Dict[str, Any]]:
        """Read and parse input trace file."""
        events = []

        try:
            with open(input_file, 'r') as f:
                for line_num, line in enumerate(f, 1):
                    line = line.strip()

                    # Skip comments and empty lines
                    if not line or line.startswith('#'):
                        continue

                    try:
                        event = json.loads(line)
                        events.append(event)
                    except json.JSONDecodeError as e:
                        print(f"Warning: Invalid JSON on line {line_num} in {input_file}: {e}")
                        continue

        except FileNotFoundError:
            print(f"Error: Input file not found: {input_file}")
            return []
        except Exception as e:
            print(f"Error reading input file {input_file}: {e}")
            return []

        print(f"Read {len(events)} events from {input_file}")
        return events

    def _convert_events(self, events: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
        """Convert input events to TLA+ format using state tracker."""

        # Initialize state tracker
        config = self.mapping.get("config", {})
        threads = config.get("Threads", ["Thread0", "Thread1", "Thread2"])

        if self.use_universal:
            tracker = UniversalRwMutexStateTracker(threads=threads, mapping=self.mapping)
        else:
            tracker = RwMutexStateTracker(threads=threads, mapping=self.mapping)
        transitions = []

        # Add configuration header
        transitions.append(tracker.get_initial_config())

        # Process each system trace event
        for event in events:
            # Convert system event to TLA+ format using state tracker
            tla_step = tracker.apply_action(event)
            transitions.append(tla_step)

        return transitions

    def _write_output_trace(self, transitions: List[Dict[str, Any]], output_file: str) -> None:
        """Write transitions to output file in NDJSON format."""
        os.makedirs(os.path.dirname(output_file), exist_ok=True)

        with open(output_file, 'w') as f:
            for transition in transitions:
                f.write(json.dumps(transition) + '\n')

        print(f"Wrote {len(transitions)} transitions to {output_file}")

    def discover_threads_in_trace(self, trace_file: str) -> Set[str]:
        """
        Discover all thread IDs used in a converted trace file.

        Args:
            trace_file: Path to NDJSON trace file

        Returns:
            Set of thread IDs found in the trace
        """
        threads = set()

        try:
            with open(trace_file, 'r') as f:
                for line_num, line in enumerate(f, 1):
                    if not line.strip():
                        continue
                    try:
                        entry = json.loads(line)

                        # First line contains thread configuration
                        if line_num == 1 and "Threads" in entry:
                            threads.update(entry["Threads"])
                            continue

                        # Extract threads from thread_state updates
                        if "thread_state" in entry:
                            for update in entry["thread_state"]:
                                if "args" in update and len(update["args"]) > 0:
                                    thread_states = update["args"][0]
                                    if isinstance(thread_states, dict):
                                        threads.update(thread_states.keys())

                    except json.JSONDecodeError as e:
                        print(f"Warning: JSON decode error in {trace_file} line {line_num}: {e}")

        except FileNotFoundError:
            print(f"Warning: Trace file not found: {trace_file}")

        return threads

    def update_tla_config(self, threads: Set[str]) -> bool:
        """
        Update TLA+ configuration files with the discovered threads.

        Args:
            threads: Set of thread IDs to configure

        Returns:
            True if successful, False otherwise
        """
        if not self.auto_update_tla_config:
            return True

        try:
            base_path = self.project_root / "output/trace_validation/rwmutex/system_trace_gen/specula_claude"
            thread_list = sorted(list(threads))
            thread_set = "{" + ", ".join(f'"{t}"' for t in thread_list) + "}"

            # Update rwmutex.cfg
            rwmutex_cfg_path = base_path / "rwmutex.cfg"
            rwmutex_content = f"""SPECIFICATION Spec

CONSTANTS
    Threads = {thread_set}
"""
            with open(rwmutex_cfg_path, 'w') as f:
                f.write(rwmutex_content)

            # Update specTrace.cfg
            spec_trace_cfg_path = base_path / "specTrace.cfg"
            spec_trace_content = f"""CONSTANTS
    Threads = {thread_set}
    Nil <- TraceNil
    Vars <- vars
    Default <- DefaultImpl
    BaseInit <- Init
    UpdateVariables <- UpdateVariablesImpl
    TraceNext <- TraceNextImpl

SPECIFICATION TraceSpec

VIEW TraceView

POSTCONDITION TraceAccepted

CHECK_DEADLOCK FALSE
"""
            with open(spec_trace_cfg_path, 'w') as f:
                f.write(spec_trace_content)

            print(f"✅ Updated TLA+ configs with threads: {thread_list}")
            return True

        except Exception as e:
            print(f"❌ Failed to update TLA+ config: {e}")
            return False

    def copy_trace_for_validation(self, source_trace: str) -> bool:
        """
        Copy a trace file to the TLA+ validation directory.

        Args:
            source_trace: Path to source trace file

        Returns:
            True if successful, False otherwise
        """
        try:
            base_path = self.project_root / "output/trace_validation/rwmutex/system_trace_gen/specula_claude"
            target_path = base_path / "trace.ndjson"

            # Copy the trace file
            with open(source_trace, 'r') as src:
                with open(target_path, 'w') as dst:
                    dst.write(src.read())

            print(f"📁 Copied trace to: {target_path}")
            return True

        except Exception as e:
            print(f"❌ Failed to copy trace: {e}")
            return False

    def run_tla_validation(self) -> Tuple[bool, str]:
        """
        Run TLA+ validation on the configured trace.

        Returns:
            Tuple of (success, output)
        """
        try:
            base_path = self.project_root / "output/trace_validation/rwmutex/system_trace_gen/specula_claude"
            working_dir = str(base_path)

            # Build command
            cmd = [
                "java", "-cp", "/home/ubuntu/LLM_gen/spec_rag_system/tlc_tools/tla2tools.jar",
                "tlc2.TLC", "-config", "specTrace.cfg", "specTrace.tla"
            ]

            # Set environment variable
            env = os.environ.copy()
            env["TRACE_PATH"] = "trace.ndjson"

            # Run TLC
            result = subprocess.run(
                cmd,
                cwd=working_dir,
                env=env,
                capture_output=True,
                text=True,
                timeout=60
            )

            success = result.returncode == 0
            output = result.stdout + result.stderr

            return success, output

        except subprocess.TimeoutExpired:
            return False, "TLA+ validation timed out"
        except Exception as e:
            return False, f"TLA+ validation error: {e}"

    def validate_trace(self, trace_file: str) -> Dict[str, Any]:
        """
        Validate a single trace file with automatic configuration.

        Args:
            trace_file: Path to trace file

        Returns:
            Dictionary with validation results
        """
        print(f"\n🔍 Validating: {os.path.basename(trace_file)}")

        result = {
            "trace_file": trace_file,
            "success": False,
            "threads_discovered": [],
            "config_updated": False,
            "trace_copied": False,
            "tla_validation": False,
            "output": "",
            "error": None
        }

        try:
            # Step 1: Discover threads
            threads = self.discover_threads_in_trace(trace_file)
            result["threads_discovered"] = sorted(list(threads))
            print(f"   Threads found: {result['threads_discovered']}")

            if not threads:
                result["error"] = "No threads discovered in trace"
                return result

            # Step 2: Update TLA+ configuration
            if self.update_tla_config(threads):
                result["config_updated"] = True
            else:
                result["error"] = "Failed to update TLA+ configuration"
                return result

            # Step 3: Copy trace for validation
            if self.copy_trace_for_validation(trace_file):
                result["trace_copied"] = True
            else:
                result["error"] = "Failed to copy trace file"
                return result

            # Step 4: Run TLA+ validation
            tla_success, tla_output = self.run_tla_validation()
            result["tla_validation"] = tla_success
            result["output"] = tla_output

            if tla_success:
                result["success"] = True
                print("   ✅ Validation PASSED")
            else:
                print("   ❌ Validation FAILED")
                # Extract error summary
                if "Error:" in tla_output:
                    error_lines = [line.strip() for line in tla_output.split('\n')
                                 if 'Error:' in line or 'Failed matching' in line]
                    if error_lines:
                        result["error"] = error_lines[0]

        except Exception as e:
            result["error"] = str(e)
            print(f"   ❌ Exception: {e}")

        return result

    def batch_validate_traces(self, trace_directory: str) -> Dict[str, Any]:
        """
        Batch validate all traces in a directory.

        Args:
            trace_directory: Path to directory containing trace files

        Returns:
            Dictionary with batch validation results
        """
        print(f"🚀 Starting batch validation of traces in: {trace_directory}")

        trace_files = []
        for file_path in Path(trace_directory).glob("*.ndjson"):
            trace_files.append(str(file_path))

        trace_files.sort()

        if not trace_files:
            print("❌ No NDJSON trace files found")
            return {"error": "No trace files found", "results": []}

        print(f"📋 Found {len(trace_files)} trace files")

        results = []
        success_count = 0

        for trace_file in trace_files:
            result = self.validate_trace(trace_file)
            results.append(result)

            if result["success"]:
                success_count += 1

        # Summary
        print(f"\n📊 BATCH VALIDATION SUMMARY")
        print(f"Total traces: {len(trace_files)}")
        print(f"Successful validations: {success_count}")
        print(f"Failed validations: {len(trace_files) - success_count}")

        if success_count < len(trace_files):
            print("\n❌ Failed traces:")
            for result in results:
                if not result["success"]:
                    filename = os.path.basename(result["trace_file"])
                    error = result.get("error", "Unknown error")
                    print(f"   - {filename}: {error}")

        return {
            "total": len(trace_files),
            "success": success_count,
            "failed": len(trace_files) - success_count,
            "results": results
        }