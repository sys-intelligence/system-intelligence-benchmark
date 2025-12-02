"""
ZooKeeper trace converter implementation.

Converts ZooKeeper traces from various formats to TLA+ specification-compatible
NDJSON format for validation.
"""

import json
from pathlib import Path
from typing import Dict, Any

from ..base import TraceConverter


class ZooKeeperTraceConverter(TraceConverter):
    """
    Convert ZooKeeper traces to TLA+ spec-compatible format.

    Handles conversion from:
    - Remix JSON format (model-level traces)
    - System-level NDJSON (from instrumented ZooKeeper)

    To standardized NDJSON format for TLA+ validation.
    """

    def __init__(self, spec_path: str = None):
        """
        Initialize converter.

        Args:
            spec_path: Optional path to TLA+ specification for action mapping
        """
        self.spec_path = spec_path
        self._load_action_mapping()

    def _load_action_mapping(self):
        """
        Load action name mapping from Remix to TLA+ spec.

        Maps Remix event names to corresponding TLA+ action names.
        This mapping may be customized based on the specific TLA+ spec.
        """
        # Default mapping from Remix events to common TLA+ action names
        self.action_mapping = {
            # Initialization
            "SetInitState": "Init",

            # Leader election
            "Notification": "SendNotification",
            "ElectionAndDiscovery": "ElectLeader",

            # Follower actions
            "FollowerProcessPROPOSAL": "FollowerHandleProposal",
            "FollowerProcessCOMMIT": "FollowerHandleCommit",
            "FollowerProcessNEWLEADER": "FollowerHandleNewLeader",
            "FollowerProcessUPTODATE": "FollowerHandleUpToDate",
            "FollowerProcessNEWLEADERAfterCurrentEpochUpdated": "FollowerAckNewLeader",

            # Leader actions
            "LeaderProcessACK": "LeaderHandleAck",
            "LeaderProcessACKLD": "LeaderHandleAckLeaderDiff",
            "LeaderSyncFollower": "LeaderSyncFollower",
            "LeaderProcessRequest": "LeaderHandleRequest",

            # Sync actions
            "FollowerProcessSyncMessage": "FollowerSync",

            # Node lifecycle
            "NodeStart": "StartNode",
            "NodeCrash": "CrashNode",

            # Partitions
            "PartitionStart": "StartPartition",
            "PartitionStop": "StopPartition",
        }

    def convert_trace(self, input_path: Path, output_path: Path) -> Dict[str, Any]:
        """
        Convert ZooKeeper trace to TLA+ spec-compatible format.

        Args:
            input_path: Path to raw trace file (JSON or NDJSON)
            output_path: Path for converted trace file

        Returns:
            Dictionary with conversion results:
            {
                "success": bool,
                "input_events": int,
                "output_transitions": int,
                "output_file": str,
                "error": str (if failed)
            }
        """
        try:
            print(f"Converting ZooKeeper trace from {input_path} to {output_path}")

            # Read input trace
            events = self._read_input_trace(input_path)

            if not events:
                return {
                    "success": False,
                    "error": "No events found in input trace"
                }

            # Convert format
            converted_events = self._convert_events(events)

            # Write output
            self._write_output_trace(converted_events, output_path)

            return {
                "success": True,
                "input_events": len(events),
                "output_transitions": len(converted_events),
                "output_file": str(output_path)
            }

        except Exception as e:
            return {
                "success": False,
                "error": f"Conversion failed: {str(e)}"
            }

    def _read_input_trace(self, input_path: Path) -> list:
        """
        Read input trace file.

        Handles both JSON array format (Remix) and NDJSON format.

        Args:
            input_path: Path to input file

        Returns:
            List of event dictionaries
        """
        with open(input_path, 'r') as f:
            content = f.read().strip()

            # Try JSON array format first (Remix format)
            if content.startswith('['):
                try:
                    events = json.loads(content)
                    # Skip metadata if present
                    if events and 'version' in events[0]:
                        return events[1:]
                    return events
                except json.JSONDecodeError:
                    pass

            # Try NDJSON format
            events = []
            for line in content.split('\n'):
                line = line.strip()
                if line:
                    try:
                        events.append(json.loads(line))
                    except json.JSONDecodeError:
                        continue

            return events

    def _convert_events(self, events: list) -> list:
        """
        Convert events to standardized format.

        Args:
            events: List of input event dictionaries

        Returns:
            List of converted event dictionaries
        """
        converted = []

        for i, event in enumerate(events):
            # Extract action name
            action_name = self._extract_action_name(event)

            if not action_name:
                continue

            # Map to TLA+ action name if mapping exists
            tla_action = self.action_mapping.get(action_name, action_name)

            # Build standardized event
            converted_event = {
                "event": tla_action,
                "step": event.get("step", event.get("Step", i)),
                "node": self._extract_node_id(event),
            }

            # Add event-specific data
            event_data = self._extract_event_data(event, action_name)
            if event_data:
                converted_event["data"] = event_data

            converted.append(converted_event)

        return converted

    def _extract_action_name(self, event: Dict) -> str:
        """
        Extract action name from event.

        Handles different event formats.

        Args:
            event: Event dictionary

        Returns:
            Action name string or empty string if not found
        """
        # Check direct 'event' field (NDJSON format)
        if "event" in event:
            return event["event"]

        # Check Remix JSON format (first non-Step key is action name)
        for key in event.keys():
            if key not in ["Step", "step"]:
                return key

        return ""

    def _extract_node_id(self, event: Dict) -> str:
        """
        Extract node ID from event.

        Args:
            event: Event dictionary

        Returns:
            Node ID string
        """
        # Direct node field
        if "node" in event:
            return event["node"]

        # Remix format
        if "event" in event and isinstance(event["event"], dict):
            event_data = event["event"]
        else:
            # Find action data (first non-Step value)
            event_data = None
            for key, value in event.items():
                if key not in ["Step", "step"] and isinstance(value, dict):
                    event_data = value
                    break

        if event_data:
            # Try different node ID fields
            for field in ["nodeId", "node", "serverId", "sid"]:
                if field in event_data:
                    return str(event_data[field])

        return ""

    def _extract_event_data(self, event: Dict, action_name: str) -> Dict:
        """
        Extract event-specific data.

        Args:
            event: Event dictionary
            action_name: Name of the action

        Returns:
            Dictionary of event data
        """
        # If event has 'data' field, use it directly
        if "data" in event:
            return event["data"]

        # For Remix format, extract action data
        if action_name in event:
            return event[action_name]

        # Extract from nested structure
        data = {}
        for key, value in event.items():
            if key not in ["Step", "step", "event", "node"]:
                data[key] = value

        return data

    def _write_output_trace(self, events: list, output_path: Path):
        """
        Write converted events to NDJSON file.

        Args:
            events: List of converted event dictionaries
            output_path: Output file path
        """
        output_path.parent.mkdir(parents=True, exist_ok=True)

        with open(output_path, 'w') as f:
            for event in events:
                f.write(json.dumps(event) + '\n')
