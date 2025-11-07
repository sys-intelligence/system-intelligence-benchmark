"""
SpinLock Trace Converter Implementation - Simple Mapping Version

Simple field mapping converter for SpinLock traces.
"""

import json
import os
from typing import Dict, Any, List, Optional
from pathlib import Path


class SpinLockTraceConverterImpl:
    """
    Simple mapping-based implementation for SpinLock trace conversion.
    """
    
    def __init__(self, mapping_file: str = None):
        """Initialize trace converter with mapping configuration."""
        if mapping_file is None:
            data_mapping = "data/convertor/spin/spin_mapping.json"
            module_mapping = os.path.join(os.path.dirname(__file__), "spin_mapping.json")
            
            if os.path.exists(data_mapping):
                mapping_file = data_mapping
            else:
                mapping_file = module_mapping
        
        self.mapping_file = mapping_file
        self.mapping = self._load_mapping()
        
    def _load_mapping(self) -> Dict[str, Any]:
        """Load mapping configuration from JSON file."""
        try:
            with open(self.mapping_file, 'r') as f:
                mapping = json.load(f)
                print(f"Loaded SpinLock mapping configuration from: {self.mapping_file}")
                return mapping
        except Exception as e:
            print(f"Failed to load mapping file {self.mapping_file}: {e}")
            return self._get_default_mapping()
    
    def _get_default_mapping(self) -> Dict[str, Any]:
        """Get default mapping configuration."""
        return {
            "config": {"Threads": ["t1", "t2", "t3"]},
            "events": {"Release": "Unlock", "default": "TryToAcquire"},
            "variables": {
                "lock_held": {
                    "system_path": ["state"],
                    "value_mapping": {"unlocked": False, "locked": True},
                    "default_value": False
                }
            },
            "thread_mapping": {"0": "t1", "1": "t2", "2": "t3"}
        }
    
    def _map_thread_id(self, thread_id: str) -> str:
        """Map system thread ID to TLA+ thread name."""
        return self.mapping.get("thread_mapping", {}).get(str(thread_id), f"t{thread_id}")
    
    def _map_event_name(self, event_name: str) -> str:
        """Map system event name to TLA+ action name."""
        events = self.mapping.get("events", {})
        return events.get(event_name, events.get("default", "Step"))
    
    def _map_variable_value(self, var_config: Dict[str, Any], raw_value: Any) -> Any:
        """Map system variable value to TLA+ format."""
        value_mapping = var_config.get("value_mapping", {})
        if str(raw_value) in value_mapping:
            return value_mapping[str(raw_value)]
        return raw_value
    
    def _convert_event(self, event: Dict[str, Any]) -> Dict[str, Any]:
        """Convert a single system event to TLA+ format."""
        # Map event name
        action = event.get("action", "")
        tla_action = self._map_event_name(action)
        
        # Build output event
        output_event = {"event": tla_action}
        
        # Process each variable
        variables_config = self.mapping.get("variables", {})
        for var_name, var_config in variables_config.items():
            if var_name == "thread_status":
                # Special handling for thread_status - need to build full thread map
                thread_mapping = self.mapping.get("thread_mapping", {})
                all_threads = list(thread_mapping.values())
                
                # Initialize all threads to idle
                thread_status_map = {t: "idle" for t in all_threads}
                
                # Update the specific thread that's acting
                acting_thread_id = str(event.get("thread", event.get("actor", "0")))
                acting_thread = self._map_thread_id(acting_thread_id)
                
                # Map the action to thread status
                value_mapping = var_config.get("value_mapping", {})
                if action in value_mapping:
                    thread_status_map[acting_thread] = value_mapping[action]
                
                mapped_value = thread_status_map
            else:
                # Standard field mapping
                system_path = var_config.get("system_path", [])
                raw_value = event
                
                for key in system_path:
                    if isinstance(raw_value, dict) and key in raw_value:
                        raw_value = raw_value[key]
                    else:
                        raw_value = var_config.get("default_value")
                        break
                
                mapped_value = self._map_variable_value(var_config, raw_value)
            
            # Add to output in TLA+ trace format
            output_event[var_name] = [{
                "op": "Update",
                "path": [],
                "args": [mapped_value]
            }]
        
        return output_event

    def _convert_action_based(self, events: List[Dict[str, Any]], output_trace_path: str) -> Dict[str, Any]:
        """Convert events using action-based mapping."""
        try:
            output_lines = []

            # First line: constants configuration
            constants = self.mapping.get("constants", {})
            config_line = json.dumps(constants)
            output_lines.append(config_line)

            # Process action mapping
            action_mapping = self.mapping.get("action_mapping", {})

            for event in events:
                system_action = event.get("action", "")

                # Find matching action in mapping
                if system_action in action_mapping:
                    mapping_config = action_mapping[system_action]
                    tla_action = mapping_config.get("tla_action", system_action)

                    # Extract parameters
                    params = {}
                    for param_name, param_config in mapping_config.get("parameters", {}).items():
                        source = param_config.get("source", "")
                        if source == "thread":
                            thread_id = str(event.get("thread", event.get("actor", "0")))
                            thread_mapping = param_config.get("mapping", {})
                            params[param_name] = thread_mapping.get(thread_id, f"t{thread_id}")
                        elif source == "lock":
                            lock_id = str(event.get("lock", "0"))
                            params[param_name] = f"lock{lock_id}"
                        else:
                            # Direct field mapping
                            params[param_name] = event.get(source, "")

                    # Build action line
                    action_line = {
                        "action": tla_action,
                    }
                    action_line.update(params)
                    output_lines.append(json.dumps(action_line))
                else:
                    print(f"Warning: Unmapped action: {system_action}")

            # Write output
            with open(output_trace_path, 'w') as f:
                for line in output_lines:
                    f.write(line + '\n')

            print(f"Action-based conversion complete: {len(events)} events -> {len(output_lines) - 1} actions")

            return {
                "success": True,
                "input_events": len(events),
                "output_transitions": len(output_lines) - 1,
                "output_file": output_trace_path
            }

        except Exception as e:
            return {
                "success": False,
                "error": f"Action-based conversion failed: {str(e)}"
            }

    def _convert_event_with_state(self, event: Dict[str, Any], cumulative_state: Dict[str, Any]) -> Dict[str, Any]:
        """Convert a single system event to TLA+ format with cumulative state."""
        # Map event name
        action = event.get("action", "")
        tla_action = self._map_event_name(action)

        # Build output event
        output_event = {"event": tla_action}

        # Get acting thread
        acting_thread_id = str(event.get("thread", event.get("actor", "0")))
        acting_thread = self._map_thread_id(acting_thread_id)

        # Process each variable in the mapping
        variables_config = self.mapping.get("variables", {})

        for var_name, var_config in variables_config.items():
            var_type = var_config.get("type", "scalar")

            if var_type == "function":
                # Handle function-type variables (guardState, pc, spinning)
                current_value = cumulative_state.get(var_name, {}).copy()
                update_rules = var_config.get("update_rules", {})

                # Check for old format compatibility
                if "event_mapping" in var_config:
                    update_rules = var_config["event_mapping"]

                if action in update_rules:
                    rule = update_rules[action]
                    if "acting_thread" in rule:
                        value = rule["acting_thread"]
                        # Handle special cases like "+1"
                        if value == "+1":
                            current_value[acting_thread] = current_value.get(acting_thread, 0) + 1
                        else:
                            current_value[acting_thread] = value

                cumulative_state[var_name] = current_value
                output_event[var_name] = [{"op": "Update", "path": [], "args": [current_value]}]

            elif var_type == "sequence":
                # Handle sequence-type variables (waitQueue)
                current_value = cumulative_state.get(var_name, [])
                update_rules = var_config.get("update_rules", {})

                if action in update_rules:
                    # Apply update rules for sequences if defined
                    rule = update_rules[action]
                    # Add logic here if needed for queue operations

                cumulative_state[var_name] = current_value
                output_event[var_name] = [{"op": "Update", "path": [], "args": [current_value]}]

            else:
                # Handle scalar variables (lockState)
                system_path = var_config.get("system_path", [])
                raw_value = event
                for key in system_path:
                    if isinstance(raw_value, dict) and key in raw_value:
                        raw_value = raw_value[key]
                    else:
                        raw_value = var_config.get("default_value")
                        break

                mapped_value = self._map_variable_value(var_config, raw_value)
                cumulative_state[var_name] = mapped_value
                output_event[var_name] = [{"op": "Update", "path": [], "args": [mapped_value]}]

        return output_event
    
    def convert_trace(self, input_trace_path: str, output_trace_path: str, config: Dict[str, Any] = None) -> Dict[str, Any]:
        """Convert trace from system format to TLA+ format."""
        try:
            print(f"Converting SpinLock trace: {input_trace_path} -> {output_trace_path}")
            
            # Ensure output directory exists
            os.makedirs(os.path.dirname(output_trace_path), exist_ok=True)
            
            # Read input events
            events = []
            with open(input_trace_path, 'r') as f:
                for line_num, line in enumerate(f):
                    line = line.strip()
                    if line and not line.startswith('#'):
                        try:
                            event = json.loads(line)
                            events.append(event)
                        except json.JSONDecodeError as e:
                            print(f"Skipping invalid JSON line {line_num}: {line[:50]}...")
                            continue
            
            if not events:
                return {"success": False, "error": "No valid events found"}
            
            print(f"Processing {len(events)} trace events...")

            # Check if mapping is action-based or state-based
            mapping_format = self.mapping.get("format", "state-based")

            if mapping_format == "action-based":
                return self._convert_action_based(events, output_trace_path)

            # Generate output for state-based format
            output_lines = []

            # First line: configuration
            config_data = self.mapping.get("config", {})
            if config_data.get("output_format") == "unquoted_identifiers" and "Threads" in config_data:
                threads = config_data["Threads"]
                config_str = '{"Threads": [' + ', '.join(threads) + ']}'
            else:
                config_str = json.dumps(config_data)
            output_lines.append(config_str)
            
            # Initialize cumulative state for all variables
            thread_mapping = self.mapping.get("thread_mapping", {})
            all_threads = list(thread_mapping.values())
            variables_config = self.mapping.get("variables", {})

            cumulative_state = {}
            for var_name, var_config in variables_config.items():
                if var_config.get("type") == "function":
                    default = var_config.get("default_value", {})
                    if isinstance(default, dict):
                        cumulative_state[var_name] = default.copy()
                    else:
                        cumulative_state[var_name] = {t: default for t in all_threads}
                elif var_config.get("type") == "sequence":
                    cumulative_state[var_name] = var_config.get("default_value", [])
                else:
                    cumulative_state[var_name] = var_config.get("default_value", "unlocked")

            # Convert each event with cumulative state
            for event in events:
                converted_event = self._convert_event_with_state(event, cumulative_state)
                output_lines.append(json.dumps(converted_event))
            
            # Write output
            with open(output_trace_path, 'w') as f:
                for line in output_lines:
                    f.write(line + '\n')
            
            print(f"Conversion complete: {len(events)} events -> {len(output_lines) - 1} transitions")
            
            return {
                "success": True,
                "input_events": len(events),
                "output_transitions": len(output_lines) - 1,
                "output_file": output_trace_path
            }
            
        except Exception as e:
            return {"success": False, "error": f"Conversion failed: {str(e)}"}