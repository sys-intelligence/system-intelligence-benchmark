"""
CURP Trace Converter Implementation

Internal implementation class for CURP trace conversion.
Converts CURP traces to TLA+ specification format for validation.
"""

import json
import os
from typing import Dict, Any, List
from collections import defaultdict


class CurpTraceConverterImpl:
    """
    Internal implementation for CURP trace conversion.

    This handles the conversion from raw CURP traces (NDJSON format)
    to the format expected by TLA+ specifications for validation.
    """

    def __init__(self, mapping_file: str = None, spec_path: str = None):
        """
        Initialize trace converter with mapping configuration.

        Args:
            mapping_file: Path to JSON mapping file (if None, looks in spec_path or default location)
            spec_path: Path to the spec directory (used to find mapping file)
        """
        if mapping_file is None:
            # Look in data/convertor/curp first, fallback to spec directory or module directory
            data_mapping = "data/convertor/curp/curp_mapping.json"
            module_mapping = os.path.join(
                os.path.dirname(__file__), "curp_mapping.json")

            if os.path.exists(data_mapping):
                mapping_file = data_mapping
            elif spec_path:
                spec_mapping = os.path.join(spec_path, "curp_mapping.json")
                if os.path.exists(spec_mapping):
                    mapping_file = spec_mapping
                else:
                    mapping_file = module_mapping  # fallback to module directory
            else:
                mapping_file = module_mapping

        self.mapping_file = mapping_file
        self.spec_path = spec_path
        self.mapping = self._load_mapping()

    def _load_mapping(self) -> Dict[str, Any]:
        """Load mapping configuration from JSON file."""
        try:
            with open(self.mapping_file, 'r') as f:
                return json.load(f)
        except Exception as e:
            print(f"Failed to load mapping file {self.mapping_file}: {e}")
            return {}

    def _extract_value_from_event(self, event: Dict[str, Any], path: List[str], default_value: Any = None) -> Any:
        """Extract value from event using dot notation path."""
        current = event
        try:
            for key in path:
                if isinstance(current, dict) and key in current:
                    current = current[key]
                else:
                    return default_value
            return current
        except:
            return default_value

    def _map_node_id(self, node_id: str) -> str:
        """Map system node ID to TLA+ node name."""
        node_mapping = self.mapping.get("node_mapping", {})
        return node_mapping.get(str(node_id), f"n{node_id}")

    def _map_event_name(self, event_name: str) -> str:
        """Map system event name to TLA+ action name."""
        events_mapping = self.mapping.get("events", {})
        return events_mapping.get(event_name, events_mapping.get("default", "Step"))

    def _map_variable_value(self, var_config: Dict[str, Any], raw_value: Any, node_id: str) -> Any:
        """Map system variable value to TLA+ format."""
        # Apply value mapping if configured
        if "value_mapping" in var_config and raw_value is not None:
            value_mapping = var_config["value_mapping"]
            # Check for exact match first
            if str(raw_value) in value_mapping:
                return value_mapping[str(raw_value)]
            # Check for wildcard match
            if "*" in value_mapping:
                return value_mapping["*"]

        # Handle special cases
        if raw_value is None:
            return var_config.get("default_value", "Nil")

        # Convert numeric strings to numbers where appropriate
        if isinstance(raw_value, str) and raw_value.isdigit():
            return int(raw_value)

        return raw_value

    def _build_initial_state(self) -> Dict[str, Dict[str, Any]]:
        """Build initial state with default values."""
        state = defaultdict(dict)

        node_mapping = self.mapping.get("node_mapping", {})
        variables_config = self.mapping.get("variables", {})

        for node_id, node_name in node_mapping.items():
            for var_name, var_config in variables_config.items():
                state[var_name][node_name] = var_config.get("default_value")

        return state

    def _update_state_with_event(self, state: Dict[str, Dict[str, Any]], event: Dict[str, Any]) -> None:
        """Update state incrementally with a single event."""
        node_id = event.get("nid", "1")
        node_name = self._map_node_id(node_id)

        variables_config = self.mapping.get("variables", {})

        # Update each variable based on the event
        for var_name, var_config in variables_config.items():
            system_path = var_config.get("system_path", [])
            raw_value = self._extract_value_from_event(event, system_path)
            if raw_value is not None:
                mapped_value = self._map_variable_value(
                    var_config, raw_value, node_id)
                state[var_name][node_name] = mapped_value

    def convert_trace(self, input_trace_path: str, output_trace_path: str, config: Dict[str, Any] = None) -> Dict[str, Any]:
        """
        Convert trace from CURP format to TLA+ spec format.

        Args:
            input_trace_path: Path to input trace file (NDJSON)
            output_trace_path: Path for output trace file
            config: Configuration for conversion

        Returns:
            Dictionary with conversion results
        """
        try:
            # Ensure output directory exists
            os.makedirs(os.path.dirname(output_trace_path), exist_ok=True)

            # Read input trace
            events = []
            with open(input_trace_path, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line and line.startswith('{'):
                        try:
                            event = json.loads(line)
                            events.append(event)
                        except json.JSONDecodeError as e:
                            print(
                                f"Skipping invalid JSON line: {line[:100]}... Error: {e}")
                        continue

            if not events:
                return {"success": False, "error": "No valid events found in input trace"}

            # Convert using state-based mapping
            return self._convert_state_based(events, output_trace_path)

        except Exception as e:
            return {"success": False, "error": f"CURP trace conversion failed: {str(e)}"}

    def _convert_state_based(self, events: List[Dict[str, Any]], output_trace_path: str) -> Dict[str, Any]:
        """
        Convert trace using state-based mapping.
        """
        output_lines = []

        # First line: configuration
        config_line = json.dumps(self.mapping.get("config", {}))
        output_lines.append(config_line)

        # Initialize state once
        state = self._build_initial_state()

        for event in events:
            # Update state incrementally with current event
            self._update_state_with_event(state, event)

            # Map event name to TLA+ action
            event_name = event.get("name", "Step")
            tla_action = self._map_event_name(event_name)

            # Build output line
            output_event = {}

            # Add all variables with their current state
            for var_name, node_values in state.items():
                output_event[var_name] = [{
                    "op": "Update",
                    "path": [],
                    # Convert to dict for JSON serialization
                    "args": [dict(node_values)]
                }]

            # Add event name
            output_event["event"] = tla_action

            output_lines.append(json.dumps(output_event))

        # Write output trace
        with open(output_trace_path, 'w') as f:
            for line in output_lines:
                f.write(line + '\n')

        return {
            "success": True,
            "input_events": len(events),
            "output_transitions": len(output_lines) - 1,  # Exclude config line
            "output_file": output_trace_path,
            "format": "state-based"
        }

    @classmethod
    def generate_mapping_with_llm(cls, spec_file: str, model_name: str = None, output_path: str = None) -> Dict[str, Any]:
        """
        Generate a mapping configuration using LLM based on TLA+ specification.

        Args:
            spec_file: Path to TLA+ specification file
            model_name: Name of the model to use for generation
            output_path: Path to save the generated mapping (if None, saves next to spec)

        Returns:
            Dictionary with generation results
        """
        try:
            # Import LLM functionality
            from ....config import get_configured_model

            # Read the TLA+ spec
            with open(spec_file, 'r') as f:
                spec_content = f.read()

            # Load prompt template from file
            # Get the project root directory
            current_file = os.path.abspath(__file__)
            project_root = current_file
            for _ in range(5):  # Go up 5 levels from trace_converter_impl.py
                project_root = os.path.dirname(project_root)

            prompt_file = os.path.join(
                project_root, "tla_eval", "tasks", "curp", "prompts", "mapping_generation.txt"
            )

            if not os.path.exists(prompt_file):
                raise FileNotFoundError(
                    f"Prompt template not found: {prompt_file}")

            with open(prompt_file, 'r', encoding='utf-8') as f:
                prompt_template = f.read()

            # Replace placeholders in the template
            prompt = prompt_template.replace(
                "{TLA_SPEC_CODE_PLACEHOLDER}", spec_content)
            prompt = prompt.replace(
                "{IMPLEMENTATION_CODE_PLACEHOLDER}", "# CURP implementation details")
            prompt += "\n\nReturn ONLY valid JSON, no explanations or markdown."

            # Get the configured model
            model = get_configured_model(model_name)

            # Generate the mapping
            response = model.generate_tla_specification(
                source_code="",
                prompt_template=prompt
            )

            # Parse the JSON response
            try:
                # Clean up the response - remove markdown formatting if present
                json_text = response.generated_text.strip()
                if json_text.startswith('```'):
                    # Remove markdown code blocks
                    lines = json_text.split('\n')
                    json_lines = []
                    in_block = False
                    for line in lines:
                        if line.strip().startswith('```'):
                            in_block = not in_block
                        elif in_block or not line.strip().startswith('```'):
                            if not line.strip().startswith('```'):
                                json_lines.append(line)
                    json_text = '\n'.join(json_lines)

                mapping_data = json.loads(json_text)

                # Validate the structure for state-based format
                required_keys = ['config', 'events',
                                 'variables', 'node_mapping']
                for key in required_keys:
                    if key not in mapping_data:
                        raise ValueError(f"Missing required key: {key}")

                # Save the mapping file
                if output_path is None:
                    spec_dir = os.path.dirname(spec_file)
                    output_path = os.path.join(
                        spec_dir, "curp_mapping.json")

                with open(output_path, 'w') as f:
                    json.dump(mapping_data, f, indent=2)

                return {
                    "success": True,
                    "mapping_file": output_path,
                    "mapping": mapping_data
                }

            except (json.JSONDecodeError, ValueError) as e:
                return {
                    "success": False,
                    "error": f"Failed to parse LLM response as JSON: {str(e)}",
                    "response": response.generated_text[:500]
                }

        except Exception as e:
            return {"success": False, "error": f"Failed to generate CURP mapping: {str(e)}"}
