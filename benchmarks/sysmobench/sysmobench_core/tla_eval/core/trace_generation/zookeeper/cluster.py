"""
ZooKeeper cluster management using Remix infrastructure.

This module provides a Python interface to the Remix system for generating
ZooKeeper traces through:
1. TLC model checker for generating model-level traces
2. AspectJ-instrumented ZooKeeper for replaying and collecting system traces
"""

import os
import re
import json
import time
import subprocess
from pathlib import Path
from typing import Dict, Any, List, Optional


class ZooKeeperCluster:
    """
    Manages ZooKeeper cluster for trace generation using Remix.

    Workflow:
    1. Configure TLC with desired parameters
    2. Generate model-level traces using TLC
    3. Parse model traces to JSON format
    4. Replay each trace on instrumented ZooKeeper
    5. Collect system-level events as NDJSON
    """

    def __init__(self):
        """Initialize cluster with Remix paths."""
        # Path to Remix installation
        self.remix_root = Path(__file__).parent.parent.parent.parent.parent / \
                         "data" / "repositories" / "Remix"
        self.generator_dir = self.remix_root / "generator"
        self.checker_dir = self.remix_root / "checker"
        self.traces_dir = self.remix_root / "traces"
        self.output_dir = self.remix_root / "output"

        # Verify Remix installation
        if not self.remix_root.exists():
            raise FileNotFoundError(f"Remix not found at {self.remix_root}")

    def generate_batch(self, num_traces: int, config: Dict[str, Any],
                      output_dir: Path, name_prefix: str,
                      start_index: int) -> List[Dict[str, Any]]:
        """
        Generate a batch of traces.

        Steps:
        1. Update .ini config -> set simulation traces = num_traces
        2. Run TLC to generate model traces
        3. Parse model traces to JSON
        4. Replay each trace and collect NDJSON

        Args:
            num_traces: Number of traces to generate in this batch
            config: Configuration parameters
            output_dir: Directory for output NDJSON files
            name_prefix: Prefix for output filenames
            start_index: Starting index for trace numbering

        Returns:
            List of results (may include failures)
        """
        try:
            # 1. Configure TLC generation count
            self._configure_tlc(num_traces, config)

            # 2. Run TLC model checker
            tlc_success = self._run_tlc_generation()
            if not tlc_success:
                return [{"success": False, "error": "TLC generation failed"}]

            # 3. Find latest generated traces directory
            latest_trace_dir = self._find_latest_trace_dir()

            # 4. Parse raw traces to JSON
            self._parse_traces(latest_trace_dir)

            # 5. Find parsed JSON traces
            json_trace_dir = self._find_parsed_trace_dir()
            json_traces = sorted(json_trace_dir.glob("trace_*.json"))

            print(f"Found {len(json_traces)} model traces to replay")

            # 6. Replay each trace and collect NDJSON
            results = []
            for i, json_trace in enumerate(json_traces):
                output_file = output_dir / f"{name_prefix}_{start_index + i + 1:02d}.ndjson"
                result = self._replay_and_collect(json_trace, output_file, config)
                results.append(result)

                # Stop early if failure rate is too high
                failures = sum(1 for r in results if not r.get('success', False))
                if failures > len(results) * 0.5:  # >50% failure rate
                    print(f"Warning: High failure rate ({failures}/{len(results)}), stopping batch")
                    break

            return results

        except Exception as e:
            return [{"success": False, "error": str(e)}]

    def _configure_tlc(self, num_traces: int, config: Dict[str, Any]):
        """
        Modify Zab-simulate.ini configuration file.

        Key configuration items:
        - simulation traces: Controls number of traces to generate
        - simulation depth: Maximum trace length
        - Parameters: System parameters like MaxCrashes, MaxEpoch

        Args:
            num_traces: Number of traces for TLC to generate
            config: Configuration parameters from user
        """
        ini_file = self.generator_dir / "Zab-simulate.ini"

        if not ini_file.exists():
            raise FileNotFoundError(f"TLC config file not found: {ini_file}")

        content = ini_file.read_text()

        # Update simulation traces count
        content = re.sub(
            r'simulation traces:\s*\d+',
            f'simulation traces: {num_traces}',
            content
        )

        # Update simulation depth if specified
        if 'simulation_depth' in config:
            content = re.sub(
                r'simulation depth:\s*\d+',
                f'simulation depth: {config["simulation_depth"]}',
                content
            )

        # Update Parameters section if any parameter is specified
        if any(key in config for key in ['max_crashes', 'max_epoch', 'max_transactions', 'max_partitions']):
            params_pattern = r'Parameters:\s*\[([^\]]+)\]'

            def update_params(match):
                params_str = match.group(1)
                params = {}

                # Parse existing parameters
                for item in params_str.split(','):
                    if '|->' in item:
                        key, value = item.split('|->')
                        params[key.strip()] = value.strip()

                # Update parameters from config
                if 'max_crashes' in config:
                    params['MaxCrashes'] = str(config['max_crashes'])
                if 'max_epoch' in config:
                    params['MaxEpoch'] = str(config['max_epoch'])
                if 'max_transactions' in config:
                    params['MaxTransactionNum'] = str(config['max_transactions'])
                if 'max_partitions' in config:
                    params['MaxPartitions'] = str(config['max_partitions'])
                if 'max_timeout_failures' in config:
                    params['MaxTimeoutFailures'] = str(config['max_timeout_failures'])

                # Rebuild parameter string
                params_list = [f'{k} |-> {v}' for k, v in params.items()]
                return f'Parameters: [{", ".join(params_list)}]'

            content = re.sub(params_pattern, update_params, content)

        # Write back to file
        ini_file.write_text(content)
        print(f"Configured TLC to generate {num_traces} traces")

    def _run_tlc_generation(self) -> bool:
        """
        Run TLC model checker to generate model traces.

        Returns:
            True if successful, False otherwise
        """
        try:
            print("Running TLC model checker...")
            result = subprocess.run(
                ["./generate_traces.sh"],
                cwd=str(self.generator_dir),
                capture_output=True,
                text=True,
                timeout=600  # 10 minute timeout
            )

            if result.returncode == 0:
                print("TLC generation completed successfully")
                return True
            else:
                print(f"TLC generation failed: {result.stderr}")
                return False

        except subprocess.TimeoutExpired:
            print("TLC generation timed out after 10 minutes")
            return False
        except Exception as e:
            print(f"Error running TLC: {e}")
            return False

    def _find_latest_trace_dir(self) -> Path:
        """
        Find the most recently generated trace directory.

        Returns:
            Path to latest trace directory

        Raises:
            FileNotFoundError: If no trace directories exist
        """
        trace_dirs = sorted(
            self.output_dir.glob("model_random_*"),
            key=lambda p: p.stat().st_mtime,
            reverse=True
        )

        if not trace_dirs:
            raise FileNotFoundError(f"No trace directories found in {self.output_dir}")

        return trace_dirs[0]

    def _parse_traces(self, trace_dir: Path):
        """
        Parse raw TLC traces to JSON format.

        Uses Remix's trace_reader.py to convert raw traces.

        Args:
            trace_dir: Directory containing raw traces

        Raises:
            Exception: If parsing fails
        """
        try:
            print(f"Parsing traces from {trace_dir.name}...")
            result = subprocess.run(
                ["./read_latest_traces.sh"],
                cwd=str(self.generator_dir),
                capture_output=True,
                text=True,
                timeout=300  # 5 minute timeout
            )

            if result.returncode != 0:
                raise Exception(f"Trace parsing failed: {result.stderr}")

            print("Traces parsed successfully")

        except subprocess.TimeoutExpired:
            raise Exception("Trace parsing timed out")
        except Exception as e:
            raise Exception(f"Failed to parse traces: {e}")

    def _find_parsed_trace_dir(self) -> Path:
        """
        Find directory containing parsed JSON traces.

        Returns:
            Path to parsed trace directory

        Raises:
            FileNotFoundError: If no parsed directories exist
        """
        trace_dirs = sorted(
            self.traces_dir.glob("model_random_*_output"),
            key=lambda p: p.stat().st_mtime,
            reverse=True
        )

        if not trace_dirs:
            raise FileNotFoundError(f"No parsed trace directories found in {self.traces_dir}")

        return trace_dirs[0]

    def _replay_and_collect(self, json_trace: Path, output_file: Path,
                           config: Dict[str, Any]) -> Dict[str, Any]:
        """
        Replay a single trace on instrumented ZooKeeper and collect NDJSON.

        NOTE: This requires modified ReplayService.java that outputs NDJSON
        when NDJSON_OUTPUT environment variable is set.

        Args:
            json_trace: Path to model-level JSON trace
            output_file: Path for output NDJSON file
            config: Configuration parameters

        Returns:
            Result dictionary with success status and metrics
        """
        try:
            start_time = time.time()

            # Ensure output directory exists
            output_file.parent.mkdir(parents=True, exist_ok=True)

            # Prepare environment variables for Java process
            env = os.environ.copy()
            env['NDJSON_OUTPUT'] = str(output_file)  # Pass to ReplayService.java

            # Get trace directory name for replay script
            trace_dir_name = json_trace.parent.name  # e.g., "model_random_..._output"

            print(f"Replaying {json_trace.name}...")

            # Run replay with instrumented ZooKeeper
            result = subprocess.run(
                ["./replay.sh", trace_dir_name],
                cwd=str(self.remix_root / "scripts"),
                capture_output=True,
                text=True,
                env=env,
                timeout=300  # 5 minute timeout per trace
            )

            replay_time = time.time() - start_time

            # Check if NDJSON was generated
            if output_file.exists():
                event_count = self._count_events(output_file)

                return {
                    "success": True,
                    "trace_file": str(output_file),
                    "event_count": event_count,
                    "replay_time": replay_time,
                    "source_trace": str(json_trace),
                    "metadata": {
                        "model_trace": json_trace.name,
                        "trace_dir": trace_dir_name
                    }
                }
            else:
                return {
                    "success": False,
                    "error": "NDJSON file not generated",
                    "stderr": result.stderr[:500]  # Limit error message length
                }

        except subprocess.TimeoutExpired:
            return {
                "success": False,
                "error": f"Replay timed out after 5 minutes"
            }
        except Exception as e:
            return {
                "success": False,
                "error": f"Replay failed: {str(e)}"
            }

    def _count_events(self, ndjson_file: Path) -> int:
        """
        Count number of events in NDJSON file.

        Args:
            ndjson_file: Path to NDJSON trace file

        Returns:
            Number of events (non-empty lines)
        """
        if not ndjson_file.exists():
            return 0

        try:
            with open(ndjson_file, 'r') as f:
                return sum(1 for line in f if line.strip())
        except Exception:
            return 0
