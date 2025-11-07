"""
Mutex Trace Converter Implementation

Configuration-based implementation for Mutex trace conversion.
Based on the SpinLock trace converter pattern but adapted for Mutex traces.
"""

import json
import os
from typing import Dict, Any, List, Optional
from pathlib import Path
from collections import defaultdict


class MutexTraceConverterImpl:
    """
    Configuration-based implementation for Mutex trace conversion.
    
    This handles the conversion from raw Mutex traces (JSONL format)
    to the format expected by TLA+ specifications for validation.
    """
    
    def __init__(self, mapping_file: str = None):
        """
        Initialize trace converter with mapping configuration.

        Args:
            mapping_file: Path to JSON mapping file
        """
        if mapping_file is None:
            # Look in data/convertor/mutex first, fallback to module directory
            data_mapping = "data/convertor/mutex/mutex_mapping.json"
            module_mapping = os.path.join(os.path.dirname(__file__), "mutex_mapping.json")

            if os.path.exists(data_mapping):
                mapping_file = data_mapping
            else:
                mapping_file = module_mapping

        self.mapping_file = mapping_file
        self.mapping = self._load_mapping()
        self.model = self.mapping.get("model", "default")
        
    def _load_mapping(self) -> Dict[str, Any]:
        """Load mapping configuration from JSON file."""
        try:
            with open(self.mapping_file, 'r') as f:
                mapping = json.load(f)
                print(f"Loaded Mutex mapping configuration from: {self.mapping_file}")
                return mapping
        except Exception as e:
            print(f"Error loading mapping from {self.mapping_file}: {e}")
            # Return default mapping if file not found
            return self._get_default_mapping()
    
    def _get_default_mapping(self) -> Dict[str, Any]:
        """Get default mapping configuration if file not found."""
        return {
            "config": {
                "Threads": ["Thread0", "Thread1", "Thread2", "Thread3"],
                "Mutexes": ["Mutex0", "Mutex1", "Mutex2", "Mutex3"],
                "MaxSteps": 1000
            },
            "events": {
                "TryAcquireBlocking": "TryLock",
                "TryAcquireNonBlocking": "TryLock",
                "AcquireSuccess": "LockAcquired",
                "AcquireFailNonBlocking": "TryLockFailed",
                "Release": "Unlock"
            }
        }
    
    def convert_trace(self, input_file: str, output_file: str) -> Dict[str, Any]:
        """
        Convert raw mutex trace to TLA+ format.
        
        Args:
            input_file: Path to input JSONL trace file
            output_file: Path to output NDJSON trace file
            
        Returns:
            Dictionary with conversion results
        """
        try:
            print(f"Converting mutex trace: {input_file} -> {output_file}")
            
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
            
            # Convert events to TLA+ format
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
        """Convert input events to TLA+ format."""
        transitions = []
        
        # Add configuration header - model-specific
        config = self.mapping.get("config", {})
        if self.model == "gemini":
            header = {
                "Thread": self.mapping.get("Thread", ["Thread0", "Thread1", "Thread2", "Thread3"]),
                "Nil": "Nil"
            }
        elif self.model == "claude":
            header = {
                "Threads": config.get("Threads", ["Thread0", "Thread1", "Thread2", "Thread3"])
            }
        elif self.model == "gpt5":
            # Use mapped thread names from config
            threads_list = self.mapping.get("Thread", ["Thread0", "Thread1", "Thread2", "Thread3"])
            header = {
                "THREADS": threads_list
            }
        else:  # deepseek and default
            header = {
                "Threads": config.get("Threads", ["Thread0", "Thread1", "Thread2", "Thread3"]),
                "None": ["NULL"]
            }
        transitions.append(header)
        
        # Initialize mutex state tracking
        mutex_states = defaultdict(lambda: "Unlocked")
        mutex_owners = defaultdict(lambda: "Nil")  
        mutex_sequences = defaultdict(lambda: 0)
        
        event_mapping = self.mapping.get("events", {})
        
        for i, event in enumerate(events):
            # Extract event fields - handle both formats
            seq = event.get('step', event.get('seq', i))

            # Handle both string names and numeric IDs for thread/mutex
            if isinstance(event.get('thread'), str):
                thread_name = event.get('thread')
            else:
                thread_id = event.get('thread', 0)
                thread_name = f"Thread{thread_id}"

            # Apply thread name mapping if specified in model config
            if (self.model == "gemini" or self.model == "gpt5") and "thread_mapping" in self.mapping:
                thread_mapping = self.mapping["thread_mapping"]
                thread_name = thread_mapping.get(thread_name, thread_name)

            if isinstance(event.get('mutex'), str):
                mutex_name = event.get('mutex')
            else:
                mutex_id = event.get('mutex', 0)
                mutex_name = f"Mutex{mutex_id}"

            # Handle both 'event' and 'action' fields
            action = event.get('event', event.get('action', ''))
            state = event.get('state', '')
            
            # Map action to TLA+ event
            tla_event = event_mapping.get(action, action)
            
            # Update state based on action - handle actual trace events
            if action == "Lock" or action == "TryLock":
                # These are successful acquire operations
                mutex_states[mutex_name] = "Locked"
                mutex_owners[mutex_name] = thread_name
                mutex_sequences[mutex_name] += 1
            elif action == "Unlock":
                mutex_states[mutex_name] = "Unlocked"
                mutex_owners[mutex_name] = "Nil"
                mutex_sequences[mutex_name] += 1
            # Handle legacy mapped events for backward compatibility
            elif action == "TryAcquireBlocking" or action == "TryAcquireNonBlocking":
                if state == "locked":
                    mutex_states[mutex_name] = "Locked"
                else:
                    mutex_states[mutex_name] = "Unlocked"
            elif action == "AcquireSuccess":
                mutex_states[mutex_name] = "Locked"
                mutex_owners[mutex_name] = thread_name
                mutex_sequences[mutex_name] += 1
            elif action == "Release":
                mutex_states[mutex_name] = "Unlocked"
                mutex_owners[mutex_name] = "Nil"
                mutex_sequences[mutex_name] += 1
            
            # Create state snapshot for all mutexes
            all_mutex_states = {}
            all_mutex_owners = {}
            all_mutex_sequences = {}
            
            # Include states for all mutexes mentioned in config
            for mutex_name_config in config.get("Mutexes", [f"Mutex{j}" for j in range(4)]):
                all_mutex_states[mutex_name_config] = mutex_states[mutex_name_config]
                all_mutex_owners[mutex_name_config] = mutex_owners[mutex_name_config]
                all_mutex_sequences[mutex_name_config] = mutex_sequences[mutex_name_config]
            
            # Create transition record - model-specific format
            lock_state_bool = all_mutex_states.get("Mutex0", "Unlocked") == "Locked"
            holder_value = all_mutex_owners.get("Mutex0", "Nil")

            if self.model == "gemini":
                # Gemini format: lock, holder, queue, pc
                if holder_value == "Nil":
                    holder_value = "Nil"

                # Create pc (program counter) state for all threads
                pc_state = {}
                threads_list = self.mapping.get("Thread", ["Thread0", "Thread1", "Thread2", "Thread3"])
                for thread_config in threads_list:
                    if thread_config == thread_name and holder_value == thread_name and lock_state_bool:
                        pc_state[thread_config] = "in_cs"  # Thread is in critical section
                    else:
                        pc_state[thread_config] = "idle"  # Default state

                transition = {
                    "lock": [{"op": "Update", "path": [], "args": [lock_state_bool]}],
                    "holder": [{"op": "Update", "path": [], "args": [holder_value]}],
                    "queue": [{"op": "Update", "path": [], "args": [[]]}],
                    "pc": [{"op": "Update", "path": [], "args": [pc_state]}],
                    "event": tla_event,
                    "step": seq,
                    "thread": thread_name,
                    "mutex": mutex_name
                }
            elif self.model == "claude":
                # Claude format: lock, guards, waitQueue, threadState
                guards_set = [holder_value] if holder_value != "Nil" and lock_state_bool else []

                # Create threadState for all threads
                thread_state = {}
                for thread_config in config.get("Threads", []):
                    thread_state[thread_config] = "running"  # Claude uses "running"/"waiting"

                transition = {
                    "lock": [{"op": "Update", "path": [], "args": [lock_state_bool]}],
                    "guards": [{"op": "Update", "path": [], "args": [guards_set]}],
                    "waitQueue": [{"op": "Update", "path": [], "args": [[]]}],
                    "threadState": [{"op": "Update", "path": [], "args": [thread_state]}],
                    "event": tla_event,
                    "step": seq,
                    "thread": thread_name,
                    "mutex": mutex_name
                }
            elif self.model == "gpt5":
                # GPT5 format: Only Lock and Owner (core variables)
                if holder_value == "Nil":
                    holder_value = "None"

                transition = {
                    "Lock": [{"op": "Update", "path": [], "args": [lock_state_bool]}],
                    "Owner": [{"op": "Update", "path": [], "args": [holder_value]}],
                    "event": tla_event,
                    "step": seq,
                    "thread": thread_name,
                    "mutex": mutex_name
                }
            else:
                # DeepSeek and default format: lock_state, holder, wait_queue
                if holder_value == "Nil":
                    holder_value = "NULL"  # Match DeepSeek NULL constant

                transition = {
                    "lock_state": [{"op": "Update", "path": [], "args": [lock_state_bool]}],
                    "holder": [{"op": "Update", "path": [], "args": [holder_value]}],
                    "wait_queue": [{"op": "Update", "path": [], "args": [[]]}],
                    "event": tla_event,
                    "step": seq,
                    "thread": thread_name,
                    "mutex": mutex_name
                }
            
            transitions.append(transition)
        
        return transitions
    
    def _write_output_trace(self, transitions: List[Dict[str, Any]], output_file: str) -> None:
        """Write converted transitions to output file."""
        # Ensure output directory exists
        os.makedirs(os.path.dirname(output_file), exist_ok=True)
        
        with open(output_file, 'w') as f:
            for transition in transitions:
                f.write(json.dumps(transition) + '\n')
        
        print(f"Wrote {len(transitions)} transitions to {output_file}")
    
    def get_mapping_info(self) -> Dict[str, Any]:
        """Get information about the current mapping configuration."""
        return {
            "mapping_file": self.mapping_file,
            "config": self.mapping.get("config", {}),
            "events": self.mapping.get("events", {}),
            "total_event_mappings": len(self.mapping.get("events", {}))
        }