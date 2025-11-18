"""
Alloy Trace Processor: convert system traces into Alloy facts.

This module converts system execution traces (NDJSON format) into Alloy fact
constraints that can be merged with base specifications for trace validation.
"""

import json
import logging
from pathlib import Path
from typing import Dict, List, Any
from dataclasses import dataclass

logger = logging.getLogger(__name__)


@dataclass
class AlloyTraceEvent:
    """Representation of an individual trace event."""
    action: str
    thread_id: int
    timestamp: int
    additional_data: Dict[str, Any]


class AlloyTraceConverter:
    """Convert NDJSON system traces into Alloy facts."""

    def __init__(self, task_name: str, event_mappings: Dict = None):
        """
        Initialize the converter.

        Args:
            task_name: Task identifier (for example, \"spin\")
            event_mappings: Mapping between event names and Alloy constraints
        """
        self.task_name = task_name
        self.event_mappings = event_mappings or self._load_default_mappings()

    def convert_trace_file(self, trace_path: Path) -> str:
        """
        Convert an entire trace file into an Alloy fact block.

        Args:
            trace_path: NDJSON trace file path

        Returns:
            Alloy fact source as a string
        """
        logger.info(f"Converting trace file: {trace_path}")

        # 1. Parse the trace
        events = self._parse_trace_file(trace_path)
        logger.info(f"Parsed {len(events)} events from trace")

        # 2. Extract metadata
        metadata = self._extract_metadata(events)
        logger.info(f"Metadata: {metadata}")

        # 3. Generate the fact block
        facts = self._generate_facts(events, metadata)

        return facts

    def _parse_trace_file(self, trace_path: Path) -> List[AlloyTraceEvent]:
        """Parse an NDJSON trace file."""
        events = []
        with open(trace_path, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if not line or line.startswith('#'):
                    continue  # Skip empty lines and comments

                try:
                    event_data = json.loads(line)
                    event = AlloyTraceEvent(
                        action=event_data.get('action'),
                        thread_id=event_data.get('thread'),
                        timestamp=event_data.get('timestamp'),
                        additional_data=event_data
                    )
                    events.append(event)
                except json.JSONDecodeError as e:
                    logger.warning(f"Failed to parse line {line_num}: {e}")
                    continue

        return events

    def _extract_metadata(self, events: List[AlloyTraceEvent]) -> Dict:
        """Compute metadata for the trace."""
        threads = set(e.thread_id for e in events if e.thread_id is not None)
        locks = set(e.additional_data.get('lock', 0) for e in events)

        return {
            'num_events': len(events),
            'num_threads': len(threads),
            'num_locks': len(locks),
            'threads': sorted(threads),
            'locks': sorted(locks)
        }

    def _generate_facts(self, events: List[AlloyTraceEvent],
                       metadata: Dict) -> str:
        """Produce the full Alloy fact block."""
        facts = []

        # 1. Time constraint
        facts.append(f"  // Trace has exactly {metadata['num_events']} events")
        facts.append(f"  #Time = {metadata['num_events']}")
        facts.append("")

        # 2. Event-specific constraints
        for i, event in enumerate(events):
            event_fact = self._generate_event_fact(event, i)
            if event_fact:
                facts.append(event_fact)
                facts.append("")

        # 3. Wrap into a fact block
        return f"""fact TraceConstraints {{
{chr(10).join(facts)}
}}"""

    def _generate_event_fact(self, event: AlloyTraceEvent, index: int) -> str:
        """Generate the Alloy snippet for a single event."""
        # Determine the time reference for this event index
        time_ref = self._get_time_reference(index)

        # Dispatch based on the event type
        if event.action == "TryLock":
            return self._generate_trylock_fact(event, time_ref, index)
        elif event.action == "Lock":
            return self._generate_lock_fact(event, time_ref, index)
        elif event.action == "Unlock":
            return self._generate_unlock_fact(event, time_ref, index)
        else:
            logger.warning(f"Unknown action: {event.action}")
            return f"  // Unknown action: {event.action}"

    def _get_time_reference(self, index: int) -> str:
        """Return the Alloy expression referencing the nth time step."""
        if index == 0:
            return "Time.first"
        else:
            return "Time.first" + ".next" * index

    def _generate_trylock_fact(self, event: AlloyTraceEvent, time_ref: str, index: int) -> str:
        """Generate the fact body for a TryLock event."""
        thread = f"Thread{event.thread_id}"
        lock = f"Lock{event.additional_data.get('lock', 0)}"
        result = event.additional_data.get('result', 'unknown')

        if result == "success":
            return f"""  // Event {index}: {thread} TryLock {lock} (success)
  let t = {time_ref} |
    some s: State | s.time = t and
      s.thread_status[{thread}] = Trying and
      (let s' = t.next.~time |
        s'.thread_status[{thread}] = Locked and
        {thread} in s'.lock_holder[{lock}])"""
        else:
            return f"""  // Event {index}: {thread} TryLock {lock} (failure)
  let t = {time_ref} |
    some s: State | s.time = t and
      s.thread_status[{thread}] = Trying and
      (let s' = t.next.~time |
        s'.thread_status[{thread}] = Idle and
        no {thread} in s'.lock_holder[{lock}])"""

    def _generate_lock_fact(self, event: AlloyTraceEvent, time_ref: str, index: int) -> str:
        """Generate the fact body for a blocking Lock event."""
        thread = f"Thread{event.thread_id}"
        lock = f"Lock{event.additional_data.get('lock', 0)}"

        return f"""  // Event {index}: {thread} Lock {lock}
  let t = {time_ref} |
    some s: State | s.time = t and
      s.thread_status[{thread}] = Trying and
      (let s' = t.next.~time |
        s'.thread_status[{thread}] = Locked and
        {thread} in s'.lock_holder[{lock}])"""

    def _generate_unlock_fact(self, event: AlloyTraceEvent, time_ref: str, index: int) -> str:
        """Generate the fact body for an Unlock event."""
        thread = f"Thread{event.thread_id}"
        lock = f"Lock{event.additional_data.get('lock', 0)}"

        return f"""  // Event {index}: {thread} Unlock {lock}
  let t = {time_ref} |
    some s: State | s.time = t and
      s.thread_status[{thread}] = Locked and
      {thread} in s.lock_holder[{lock}] and
      (let s' = t.next.~time |
        s'.thread_status[{thread}] = Idle and
        no s'.lock_holder[{lock}])"""

    def _load_default_mappings(self) -> Dict:
        """Load default event mappings (placeholder)."""
        # TODO: load from configuration file
        return {}


# Convenience function
def create_alloy_trace_converter(task_name: str) -> AlloyTraceConverter:
    """Factory function to create an Alloy trace converter."""
    return AlloyTraceConverter(task_name)
