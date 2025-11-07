#!/usr/bin/env python3
"""
Spec Trace Generator

Generates specTrace.tla and specTrace.cfg files based on a configuration file
that describes the spec's constants, variables, and actions.
Integrated into the TLA+ benchmark framework.
"""

import yaml
import re
from typing import Dict, Any
from pathlib import Path

# Import from benchmark framework
try:
    from ...config import get_configured_model
    LLM_AVAILABLE = True
except ImportError:
    LLM_AVAILABLE = False


def _extract_yaml_from_response(response: str) -> str:
    """Extract YAML content from LLM response, handling markdown code blocks"""
    lines = response.split('\n')
    yaml_lines = []
    in_yaml_block = False
    
    for line in lines:
        # Look for YAML code block start - handle multiple backticks (3+ backticks)
        stripped_line = line.strip()
        if (stripped_line.startswith('```yaml') or stripped_line.startswith('```yml') or
            stripped_line.startswith('``````yaml') or stripped_line.startswith('``````yml') or
            re.match(r'^`{3,}ya?ml\s*$', stripped_line)):
            in_yaml_block = True
            continue
        # Look for code block end - handle multiple backticks
        elif (stripped_line == '```' or stripped_line == '``````' or 
              re.match(r'^`{3,}\s*$', stripped_line)) and in_yaml_block:
            break
        # If we're in a YAML block, collect the line
        elif in_yaml_block:
            yaml_lines.append(line)
        # If no code block found, look for YAML content directly
        elif line.strip().startswith('spec_name:') and not in_yaml_block:
            in_yaml_block = True
            yaml_lines.append(line)
    
    # If no YAML block was found, try to extract everything that looks like YAML
    if not yaml_lines:
        # Remove any leading/trailing markdown artifacts
        content = response.strip()
        # Remove multiple backticks patterns - enhanced to handle 6+ backticks
        content = re.sub(r'^`{3,}\w*\s*', '', content, flags=re.MULTILINE)
        content = re.sub(r'`{3,}\s*$', '', content, flags=re.MULTILINE)
        return content.strip()
    
    return '\n'.join(yaml_lines).strip()


class SpecTraceGenerator:
    """
    Generates trace validation TLA+ specifications from configuration.
    
    This class takes a YAML configuration describing a TLA+ specification's
    constants, variables, and actions, and generates the corresponding
    specTrace.tla and specTrace.cfg files for trace validation.
    """
    
    def __init__(self, config_data: Dict[str, Any]):
        self.config = config_data
        self.spec_name = config_data.get('spec_name', 'spec')

    def _generate_vars_definition(self) -> str:
        """Generate Vars definition from configuration variables"""
        variables = self.config.get('variables', [])
        if not variables:
            return "Vars == << >>"

        var_names = [var['name'] for var in variables]
        vars_tuple = ", ".join(var_names)
        return f"Vars == << {vars_tuple} >>"
        
    def generate_default_impl(self) -> str:
        """Generate DefaultImpl function based on variables"""
        lines = ["DefaultImpl(varName) =="]
        
        variables = self.config.get('variables', [])
        constants = self.config.get('constants', [])
        # Sort by length descending to avoid partial replacements (e.g. Server vs ServerId)
        # Filter out None values and 'Nil' constants
        const_names = sorted([c['name'] for c in constants if c.get('name') is not None and c['name'] != 'Nil'], key=len, reverse=True)
        
        for i, var in enumerate(variables):
            var_name = var['name']
            default_type = var.get('default_type', 'custom')
            
            if i == 0:
                prefix = "    CASE"
            else:
                prefix = "     []"
            
            if default_type == 'mutex_map_bool':
                lines.append(f'{prefix} varName = "{var_name}" -> [m \in TraceMutexes |-> FALSE]')
            elif default_type == 'mutex_map_sequence':
                lines.append(f'{prefix} varName = "{var_name}" -> [m \in TraceMutexes |-> <<>>]')
            elif default_type == 'mutex_map_int':
                lines.append(f'{prefix} varName = "{var_name}" -> [m \in TraceMutexes |-> 0]')
            elif default_type == 'node_map_bool':
                lines.append(f'{prefix} varName = "{var_name}" -> [n \in TraceNodes |-> FALSE]')
            elif default_type == 'node_map_sequence':
                lines.append(f'{prefix} varName = "{var_name}" -> [n \in TraceNodes |-> <<>>]')
            elif default_type == 'node_map_int':
                lines.append(f'{prefix} varName = "{var_name}" -> [n \in TraceNodes |-> 0]')
            elif default_type == 'set':
                lines.append(f'{prefix} varName = "{var_name}" -> {{}}')
            elif default_type == 'int':
                lines.append(f'{prefix} varName = "{var_name}" -> 0')
            elif default_type == 'bool':
                lines.append(f'{prefix} varName = "{var_name}" -> FALSE')
            else:
                # Custom default
                default_value = var.get('default_value', '0')
                
                # Fix escaped TLA+ operators from YAML (\\in -> \in, \\E -> \E, etc.)
                # Handle common TLA+ operators that get double-escaped in YAML
                default_value = re.sub(r'\\\\in\b', r'\\in', default_value)  # \\in -> \in
                default_value = re.sub(r'\\\\E\b', r'\\E', default_value)    # \\E -> \E
                default_value = re.sub(r'\\\\A\b', r'\\A', default_value)    # \\A -> \A
                default_value = re.sub(r'\\\\/', r'\\/', default_value)      # \\/ -> \/
                default_value = re.sub(r'\\\\\\\\', r'\\\\', default_value) # \\\\ -> \\
                
                # Replace constants with Trace<Constant>
                for const_name in const_names:
                    # Use word boundaries to avoid replacing parts of other words
                    default_value = re.sub(r'\b' + re.escape(const_name) + r'\b', f'Trace{const_name}', default_value)
                
                lines.append(f'{prefix} varName = "{var_name}" -> {default_value}')
        
        return '\n'.join(lines)
    
    def generate_update_variables(self) -> str:
        """Generate UpdateVariablesImpl function"""
        lines = ["UpdateVariablesImpl(t) =="]
        
        variables = self.config.get('variables', [])
        for var in variables:
            var_name = var['name']
            lines.append(f'    /\\ IF "{var_name}" \in DOMAIN t')
            lines.append(f'       THEN {var_name}\' = UpdateVariable({var_name}, "{var_name}", t)')
            lines.append(f'       ELSE TRUE')
        
        return '\n'.join(lines)
    
    def _process_param_source(self, param_source: str) -> str:
        """Process parameter source to determine if it needs Trace prefix.

        Rules:
        - Constants (like Server, Nil) get Trace prefix -> TraceServer, TraceNil
        - Variables (like messages, log, matchIndex) do NOT get Trace prefix
        - DOMAIN expressions keep variables unchanged -> DOMAIN messages
        - Expressions with constants get those constants prefixed
        """
        # Get lists of variables and constants
        variables = [var['name'] for var in self.config.get('variables', [])]
        constants = [c['name'] for c in self.config.get('constants', [])]

        # Special case: DOMAIN expression
        # DOMAIN is used with variables, and variables don't get Trace prefix
        if param_source.startswith('DOMAIN '):
            return param_source  # Keep as is (e.g., "DOMAIN messages")

        # If it's exactly a constant name, add Trace prefix
        if param_source in constants:
            return f"Trace{param_source}"

        # If it's exactly a variable name, keep it as is
        # Variables in TLA+ specs don't get Trace prefix
        if param_source in variables:
            return param_source

        # For expressions, only replace constants with Trace-prefixed versions
        # Variables in expressions remain unchanged
        if any(c in param_source for c in constants):
            result = param_source
            for const in constants:
                # Use word boundaries to avoid partial replacements
                import re
                result = re.sub(r'\b' + re.escape(const) + r'\b', f'Trace{const}', result)
            return result

        # Keep as is (expressions with variables, ranges like 1..10, etc.)
        return param_source

    def generate_action_predicates(self) -> str:
        """Generate action predicate functions"""
        lines = []
        
        actions = self.config.get('actions', [])
        for action in actions:
            action_name = action['name']
            parameters = action.get('parameters', [])
            
            # Determine event name - remove "Handle" prefix if present
            event_name = action_name
            if action_name.startswith('Handle'):
                event_name = action_name[6:]  # Remove "Handle" prefix
            
            lines.append(f"Is{event_name} ==")
            lines.append(f'    /\\ IsEvent("{event_name}")')

            # Check if there's a stmt field - if so, use it directly
            stmt = action.get('stmt')

            if stmt and parameters:
                # Generate nested existential quantifiers for each parameter
                for i, param in enumerate(parameters):
                    param_name = param['name']
                    param_source = param['source']

                    # Process the source to determine if it needs Trace prefix
                    trace_source = self._process_param_source(param_source)

                    # Calculate indentation: each level adds 4 spaces
                    indent = "    " + "    " * i
                    lines.append(f'{indent}/\\ \\E {param_name} \in {trace_source} :')

                # Use the stmt field directly for the action call
                call_indent = "    " + "    " * len(parameters)
                lines.append(f'{call_indent}{stmt}')

            elif parameters:
                # No stmt, generate based on parameters
                for i, param in enumerate(parameters):
                    param_name = param['name']
                    param_source = param['source']

                    # Process the source to determine if it needs Trace prefix
                    trace_source = self._process_param_source(param_source)

                    # Calculate indentation: each level adds 4 spaces
                    indent = "    " + "    " * i
                    lines.append(f'{indent}/\\ \\E {param_name} \in {trace_source} :')

                # Generate the action call with proper indentation
                call_indent = "    " + "    " * len(parameters)
                param_names = [p['name'] for p in parameters]
                param_str = ', '.join(param_names)
                lines.append(f'{call_indent}{action_name}({param_str})')

            else:
                # No parameters case
                stmt = action.get('stmt', action_name)
                if stmt != action_name:
                    # Multi-line statement, preserve formatting
                    stmt_lines = stmt.split('\n')
                    for j, stmt_line in enumerate(stmt_lines):
                        if stmt_line.strip():  # Skip empty lines
                            if j == 0:
                                lines.append(f'    /\\ {stmt_line.strip()}')
                            else:
                                lines.append(f'       {stmt_line.strip()}')
                else:
                    lines.append(f'    /\\ {action_name}')
            
            lines.append("")
        
        return '\n'.join(lines[:-1])  # Remove last empty line
    
    def generate_interactions_predicate(self) -> str:
        """Generate IsInter predicate for interactions"""
        interactions = self.config.get('interactions', []) or self.config.get('Interactions', [])
        if not interactions:
            return ""
        
        lines = ["IsInter == "]
        lines.append("    /\\ pc # Nil")
        lines.append("    /\\ UNCHANGED <<l>>")
        
        for i, interaction in enumerate(interactions):
            interaction_name = interaction['name']
            if i == 0:
                lines.append(f"    /\\ \\/ {interaction_name}")
            else:
                lines.append(f"       \\/ {interaction_name}")
        
        return '\n'.join(lines)
    
    def generate_trace_next(self) -> str:
        """Generate TraceNextImpl function"""
        lines = ["TraceNextImpl =="]
        
        actions = self.config.get('actions', [])
        for i, action in enumerate(actions):
            action_name = action['name']
            # Determine event name - remove "Handle" prefix if present
            event_name = action_name
            if action_name.startswith('Handle'):
                event_name = action_name[6:]  # Remove "Handle" prefix
                
            if i == 0:
                lines.append(f"    \\/ Is{event_name}")
            else:
                lines.append(f"    \\/ Is{event_name}")
        
        # Add interactions if they exist
        interactions = self.config.get('interactions', []) or self.config.get('Interactions', [])
        if interactions:
            lines.append("    \\/ IsInter")
        
        return '\n'.join(lines)
    
    def generate_trace_sources(self) -> str:
        """Generate trace source definitions automatically from constants"""
        lines = []
        
        constants = self.config.get('constants', [])
        for constant in constants:
            const_name = constant['name']
            # Skip Nil as it's handled specially
            if const_name == 'Nil':
                continue
            trace_name = f"Trace{const_name}"
            lines.append(f"{trace_name} == ToSet(Trace[1].{const_name})")
        
        return '\n'.join(lines)
    
    def generate_tla_file(self) -> str:
        """Generate the complete TLA+ file"""
        action_predicates = self.generate_action_predicates()
        interactions_predicate = self.generate_interactions_predicate()
        
        # Combine action predicates and interactions predicate
        all_predicates = action_predicates
        if interactions_predicate:
            all_predicates += "\n\n" + interactions_predicate
        
        template = f"""--------------------------- MODULE specTrace ---------------------------

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, {self.spec_name}, TraceSpec, TVOperators

TraceNil == "null"

(* Extract system configuration from first trace line *)
{self.generate_trace_sources()}

(* Default variable initialization *)
{self.generate_default_impl()}

(* State variable update logic *)
{self.generate_update_variables()}

(* Action event matching *)

{all_predicates}

(* State transition definition *)
{self.generate_trace_next()}


(* REPLACE / MODIFY COMMENT BELOW ONLY IF YOU WANT TO MAKE ACTION COMPOSITION *)
ComposedNext == FALSE

(* NOTHING TO CHANGE BELOW *)
BaseSpec == Init /\\ [][Next \\/ ComposedNext]_Vars

=============================================================================

"""
        return template
    
    def generate_cfg_file(self) -> str:
        """Generate the TLC configuration file"""
        cfg_lines = ["CONSTANTS"]
        
        # Add user-defined constants with their values
        constants = self.config.get('constants', [])
        for constant in constants:
            const_name = constant['name']
            const_value = constant.get('value', '')
            if const_value:
                cfg_lines.append(f"    {const_name} = {const_value}")
            else:
                cfg_lines.append(f"    {const_name}")
        
        # Add base configuration constants (always present)
        cfg_lines.extend([
            "    Nil <- TraceNil",
            "    Vars <- vars",
            "    Default <- DefaultImpl", 
            "    BaseInit <- Init",
            "    UpdateVariables <- UpdateVariablesImpl",
            "    TraceNext <- TraceNextImpl"
        ])
        
        # Add other standard configuration
        cfg_lines.extend([
            "",
            "SPECIFICATION TraceSpec",
            "",
            "VIEW TraceView",
            "",
            "POSTCONDITION TraceAccepted",
            "",
            "CHECK_DEADLOCK FALSE"
        ])
        
        return '\n'.join(cfg_lines)
    
    def generate_files(self, output_dir: str) -> Dict[str, str]:
        """
        Generate both TLA+ and CFG files
        
        Returns:
            Dictionary with file paths of generated files
        """
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Generate TLA+ file
        tla_content = self.generate_tla_file()
        tla_file = output_path / "specTrace.tla"
        with open(tla_file, 'w') as f:
            f.write(tla_content)
        
        # Generate CFG file
        cfg_content = self.generate_cfg_file()
        cfg_file = output_path / "specTrace.cfg"
        with open(cfg_file, 'w') as f:
            f.write(cfg_content)
        
        return {
            "tla_file": str(tla_file),
            "cfg_file": str(cfg_file)
        }


def generate_config_from_tla(tla_file: str, cfg_file: str, model_name: str = None) -> Dict[str, Any]:
    """
    Automatically generate configuration from TLA+ and CFG files using LLM
    
    Args:
        tla_file: Path to the TLA+ specification file
        cfg_file: Path to the TLC configuration file  
        model_name: Name of the model to use for generation
        
    Returns:
        Generated configuration as dictionary
    """
    if not LLM_AVAILABLE:
        raise ImportError("LLM client not available. Please install required dependencies.")
    
    # Read TLA+ and CFG files
    try:
        with open(tla_file, 'r') as f:
            tla_content = f.read()
    except Exception as e:
        raise Exception(f"Error reading TLA+ file {tla_file}: {e}")
    
    try:
        with open(cfg_file, 'r') as f:
            cfg_content = f.read()
    except Exception as e:
        raise Exception(f"Error reading CFG file {cfg_file}: {e}")
    
    # Read prompt template
    current_dir = Path(__file__).parent.parent.parent
    prompt_file = current_dir / "tasks" / "etcd" / "prompts" / "trace_config_generation.txt"
    
    try:
        with open(prompt_file, 'r') as f:
            prompt_template = f.read()
    except Exception as e:
        raise Exception(f"Error reading prompt file {prompt_file}: {e}")
    
    # Prepare input content
    input_content = f"""TLA+ Specification (.tla file):
```tla
{tla_content}
```

TLC Configuration (.cfg file):
```cfg
{cfg_content}
```"""
    
    # Get LLM client and generate configuration
    try:
        from ...config import get_config_manager
        config_manager = get_config_manager()
        model = config_manager.get_model(model_name)
        
        # Create a simple prompt without using format()
        full_prompt = prompt_template.replace("{source_code}", input_content)
        
        # Generate response using direct API call
        response = model.generate_tla_specification(
            source_code="",  # Empty since we already embedded content in prompt
            prompt_template=full_prompt
        )
        
        # Parse YAML response
        # Extract YAML content from markdown code blocks
        yaml_content = _extract_yaml_from_response(response.generated_text)
        
        # Validate YAML content before parsing
        if not yaml_content.strip():
            raise Exception("No YAML content extracted from LLM response")
        
        try:
            config_data = yaml.safe_load(yaml_content)
            return config_data
        except yaml.YAMLError as e:
            # Provide more detailed error information
            raise Exception(f"YAML parsing error: {e}\n\nExtracted YAML content:\n{yaml_content[:500]}...")
        
    except Exception as e:
        raise Exception(f"Error generating configuration with LLM: {e}")