"""
Trace-based method implementation with automatic error correction.

This method generates TLA+ specifications and automatically detects and corrects
syntax and semantic errors using iterative LLM feedback.
"""

import json
import logging
import re
from random import sample
import time
from typing import Dict, Any
from pathlib import Path

from tla_eval.methods.agent_based.method import AgentBasedMethod

from ..base import TLAGenerationMethod, GenerationTask, GenerationOutput, format_prompt_template
from ...config import get_configured_model
from ...core.verification.validators import TLAValidator, ValidationResult
from ...models.base import GenerationConfig

logger = logging.getLogger(__name__)

MAX_TRACE_SIZE_BYTES = 512 * 1024  # 1 MB cap when sampling traces


class TraceBasedMethod(AgentBasedMethod):
    """
    Trace-based method for TLA+ generation with automatic error correction, based on the AgentBasedMethod.
    
    This method implements the same feedback loop, but provides the traces as input instead of the codebase.
    """
    
    def __init__(self, max_correction_attempts: int = 3, validation_timeout: int = 30):
        """
        Initialize trace-based method.
        
        Args:
            max_correction_attempts: Maximum number of correction attempts
            validation_timeout: Timeout for TLA+ validation operations
        """
        super().__init__("trace_based")
        self.max_correction_attempts = max_correction_attempts
        self.validation_timeout = validation_timeout
        self.validator = TLAValidator(timeout=validation_timeout)
        
    def generate(self, task: GenerationTask, model_name: str = None) -> GenerationOutput:
        """
        Generate TLA+ specification with automatic error correction.
        
        Args:
            task: Generation task with traces 
            model_name: Model to use from config
            
        Returns:
            GenerationOutput with corrected TLA+ specification
        """
        logger.info(f"Starting trace-based generation for task: {task.task_name}")
        
        try:
            # Get configured model
            model = get_configured_model(model_name)
            logger.info(f"Using model: {model.model_name}")
            
            # Step 1: Initial generation
            logger.info("Step 1: Initial TLA+ generation")
            initial_result = self._initial_generation(task, model)
            
            if not initial_result.success:
                logger.error(f"Initial generation failed: {initial_result.error_message}")
                return GenerationOutput(
                    tla_specification="",
                    method_name=self.name,
                    task_name=task.task_name,
                    metadata={"initial_generation_failed": True},
                    success=False,
                    error_message=initial_result.error_message
                )
            
            # Skip correction loop - return initial specification directly
            logger.info("Step 2: Skipping internal correction loop (composite evaluator will handle corrections)")
            
            # Compile metadata (no correction metadata)
            total_generation_time = initial_result.metadata.get('latency_seconds', 0)
            
            metadata = {
                "model_info": model.get_model_info(),
                "initial_generation_metadata": initial_result.metadata,
                "total_generation_time": total_generation_time,
                "method_type": "trace_based_no_internal_correction",
                "internal_correction_skipped": True
            }
            
            # Return initial specification without internal correction
            return GenerationOutput(
                tla_specification=initial_result.generated_text,
                method_name=self.name,
                task_name=task.task_name,
                metadata=metadata,
                success=True,
                error_message=None
            )
            
        except Exception as e:
            logger.error(f"Trace-based generation failed with exception: {e}")
            return GenerationOutput(
                tla_specification="",
                method_name=self.name,
                task_name=task.task_name,
                metadata={},
                success=False,
                error_message=str(e)
            )
    
    def _initial_generation(self, task: GenerationTask, model) -> Any:
        """Generate initial TLA+ specification using standard prompt."""
        prompt = self._create_initial_prompt(task)
        
        # Create generation config from model's YAML configuration
        generation_config = GenerationConfig(
            max_tokens=model.config.get('max_tokens'),
            temperature=model.config.get('temperature'),
            top_p=model.config.get('top_p')  # Only if defined in YAML
        )
        
        logger.info(f"Initial generation config from YAML: {model.config}")
        logger.debug(f"Using initial prompt ({len(prompt)} chars)")
        return model.generate_tla_specification("", prompt, generation_config) # set source code to empty, we'll process traces in the prompt

    def _create_initial_prompt(self, task: GenerationTask) -> str:
        """Create initial generation prompt."""
        from ...tasks.loader import get_task_loader
        task_loader = get_task_loader()
        prompt_template = task_loader.get_task_prompt(
            task.task_name,
            "trace_based",
            task.spec_language
        ) 

        trace_format = task.extra_info.get("trace_format")
        if not trace_format:
            raise ValueError("trace_format must be provided in task.extra_info for trace_based method")

        traces = task.traces
        if trace_format == "etcd_based" or task.extra_info.get("trace_sample", None) is not None:
            # etcd traces are large; sample a few to avoid overflowing request size/context
            sample_size = task.extra_info.get("trace_sample") or 3
            if isinstance(traces, list):
                def trace_size_bytes(trace_item: Any) -> int:
                    """Return approximate size of a trace item in bytes for filtering."""
                    if isinstance(trace_item, list):
                        return sum(len(content.encode("utf-8")) for _, content in trace_item)
                    if isinstance(trace_item, tuple) and len(trace_item) >= 2:
                        return len(trace_item[1].encode("utf-8"))
                    return 0

                eligible_traces = [trace for trace in traces if trace_size_bytes(trace) <= MAX_TRACE_SIZE_BYTES]
                if len(eligible_traces) < len(traces):
                    logger.info(
                        "Filtered %d trace(s) over %d bytes for task %s",
                        len(traces) - len(eligible_traces),
                        MAX_TRACE_SIZE_BYTES,
                        task.task_name,
                    )

                traces = eligible_traces
                if len(traces) > sample_size:
                    traces = sample(traces, sample_size)

        trace_str = ""
        # Iterate over the possibly-sampled traces, not the original task.traces
        for i, distributed_trace in enumerate(traces):
            if isinstance(distributed_trace, list):
                trace_str += f"## Execution #{i+1}:\n"
                for trace_name, trace_content in distributed_trace:
                    formatted_trace = trace_content
                    if trace_name.endswith(('.ndjson', '.jsonl')):
                        converted = self._convert_ndjson_to_tsv(trace_content)
                        if converted:
                            formatted_trace = converted
                    trace_str += f"{trace_name}:\n```\n{formatted_trace}\n```\n"
                trace_str += "\n"
            elif isinstance(distributed_trace, tuple):
                trace_name, trace_content = distributed_trace
                formatted_trace = trace_content
                if trace_name.endswith(('.ndjson', '.jsonl')):
                    converted = self._convert_ndjson_to_tsv(trace_content)
                    if converted:
                        formatted_trace = converted
                trace_str += f"## Execution #{i+1}:\n{trace_name}:\n```\n{formatted_trace}\n```\n\n"

        trace_format_file = Path(f"data/trace_based/{trace_format}.txt")
        trace_format_info = trace_format_file.read_text(encoding='utf-8')
        
        # Prepare format variables
        format_vars = {
            'language': task.language,
            'description': task.description,
            'system_type': task.system_type,
            'traces': trace_str,
            'trace_format': trace_format_info,
        }
        
        # Add extra info if available
        if task.extra_info:
            format_vars.update(task.extra_info)
        
        # Format template with task information and keep literal braces intact
        return format_prompt_template(prompt_template, format_vars)

    def _convert_ndjson_to_tsv(self, ndjson_str: str) -> str:
        """Convert NDJSON payload into TSV while abbreviating long capitalized values."""

        value_to_abbreviation: Dict[str, str] = {}
        abbreviation_order: list[tuple[str, str]] = []
        used_abbreviations: set[str] = set()

        def should_abbreviate(text: str) -> bool:
            return len(text) >= 5 and text[:1].isupper()

        def segment_value(text: str) -> list[str]:
            normalized = re.sub(r"[_-]+", " ", text)
            if " " in normalized:
                return [seg for seg in normalized.split() if seg]
            segments = re.findall(r"[A-Z][a-z0-9]*|[0-9]+", normalized)
            return segments or [normalized]

        def build_abbreviation(text: str) -> str:
            existing = value_to_abbreviation.get(text)
            if existing:
                return existing

            segments = segment_value(text)
            positions = [1] * len(segments)

            def make_candidate() -> str:
                return "".join(seg[:pos].upper() for seg, pos in zip(segments, positions)) or text[:1].upper()

            candidate = make_candidate()
            while not candidate or candidate in used_abbreviations:
                progressed = False
                for idx in range(len(segments)):
                    if positions[idx] < len(segments[idx]):
                        positions[idx] += 1
                        progressed = True
                        break
                if not progressed:
                    suffix = 2
                    base = candidate or text[:1].upper() or "V"
                    while f"{base}{suffix}" in used_abbreviations:
                        suffix += 1
                    candidate = f"{base}{suffix}"
                    break
                else:
                    candidate = make_candidate()

            used_abbreviations.add(candidate)
            value_to_abbreviation[text] = candidate
            abbreviation_order.append((candidate, text))
            return candidate

        def sanitize_scalar(value: Any) -> str:
            if isinstance(value, bool):
                return "true" if value else "false"
            if value is None:
                return ""
            if isinstance(value, str):
                sanitized = value.replace("\t", " ").replace("\n", " ").strip()
                if should_abbreviate(sanitized):
                    return build_abbreviation(sanitized)
                return sanitized
            sanitized = str(value)
            return sanitized.replace("\t", " ").replace("\n", " ").strip()

        def list_to_string(items: list[Any]) -> str:
            if not items:
                return "[]"
            parts = []
            for item in items:
                if isinstance(item, dict):
                    nested_parts = []
                    for key, nested_val in item.items():
                        nested_str = sanitize_scalar(nested_val)
                        if nested_str:
                            nested_parts.append(f"{key} {nested_str}")
                        else:
                            nested_parts.append(str(key))
                    parts.append(" ".join(nested_parts).strip())
                elif isinstance(item, list):
                    parts.append(list_to_string(item))
                else:
                    parts.append(sanitize_scalar(item))
            return "|".join(filter(None, parts))

        def flatten_value(prefix: str, value: Any, collector: Dict[str, str]) -> None:
            if isinstance(value, dict):
                if value:
                    for key, nested_val in value.items():
                        child_prefix = f"{prefix}.{key}" if prefix else str(key)
                        flatten_value(child_prefix, nested_val, collector)
                else:
                    collector[prefix] = "{}"
                return
            if isinstance(value, list):
                collector[prefix] = list_to_string(value)
                return
            collector[prefix] = sanitize_scalar(value)

        lines = [line for line in ndjson_str.splitlines() if line.strip() and not line.startswith("#")]
        if not lines:
            return ""

        records: list[Dict[str, str]] = []
        field_order: list[str] = []
        for line in lines:
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                logger.debug("Skipping malformed NDJSON line: %s", line)
                continue
            if not isinstance(obj, dict):
                continue
            flat_record: Dict[str, str] = {}
            for key, value in obj.items():
                flatten_value(str(key), value, flat_record)
            records.append(flat_record)
            for column_name in flat_record.keys():
                if column_name not in field_order:
                    field_order.append(column_name)

        if not records:
            return ""

        header = "\t".join(field_order)
        rows = [header]

        for record in records:
            row_values = []
            for field in field_order:
                value = record.get(field)
                if value is None:
                    value = ""
                row_values.append(value)
            rows.append("\t".join(row_values))

        if not abbreviation_order:
            return "\n".join(rows)

        mapping = "**Abbreviations key** " + " ".join(f"{abbr}:{original}" for abbr, original in abbreviation_order)
        rows.append("")
        rows.append(mapping)
        return "\n".join(rows)

    
    
    def get_method_info(self) -> Dict[str, Any]:
        """Get information about trace-based method."""
        return {
            "name": self.name,
            "description": "Trace-based LLM generation with automatic error correction",
            "type": "iterative_correction",
            "requires_model": True,
            "supports_iteration": True,
            "max_correction_attempts": self.max_correction_attempts,
            "validation_timeout": self.validation_timeout,
            "features": [
                "automatic_error_detection",
                "iterative_correction",
                "syntax_validation",
                "semantic_validation"
            ]
        }
