"""
PGo Trace Validation Evaluator: System consistency evaluation for TLA+ specifications.

This evaluator implements a generic trace validation pipeline that works with
any system that provides trace generation and conversion implementations:

1. System-specific trace generation
2. LLM-based configuration generation for trace validation
3. System-specific trace format conversion 
4. TLC verification of traces against converted specifications

The system-specific logic is delegated to modules in tla_eval/core/trace_generation/{system}/
"""

import subprocess
import shutil
import time
from pathlib import Path
import traceback
from typing import Dict, Any, List
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed

from ...core.trace_generation.registry import get_system, get_available_systems, is_system_supported
from ...core.spec_processing import SpecTraceGenerator, generate_config_from_tla
from ...core.verification import TLCRunner
from ...config import get_configured_model
from ...models.base import GenerationConfig
from ..base.evaluator import BaseEvaluator
from ..base.result_types import ConsistencyEvaluationResult


class PGoTraceValidationEvaluator(BaseEvaluator):
    """
    Trace Validation Evaluator: System consistency evaluation.
    
    This evaluator implements a generic trace validation workflow that works
    with any system implementation:
    1. **System-specific Trace Generation**: Uses system modules for trace generation
    2. **Config Generation**: LLM-based YAML configuration from TLA+ specs
    3. **System-specific Conversion**: Uses system modules for trace format conversion
    4. **TLC Verification**: Trace validation against converted specifications
    """
    
    def __init__(self, 
                 spec_dir: str = "data/spec",
                 traces_dir: str = "data/sys_traces",
                 timeout: int = 600,
                 model_name: str = None,
                 max_workers: int = 4):
        """
        Initialize trace validation evaluator.
        
        Args:
            spec_dir: Directory containing TLA+ specifications
            traces_dir: Base directory to store generated traces (system subdirs created automatically)
            timeout: Timeout for evaluation operations in seconds
            model_name: Name of the model to use for specTrace generation (if None, uses default)
            max_workers: Maximum number of worker threads for concurrent trace validation
        """
        super().__init__(timeout=timeout)
        self.spec_dir = Path(spec_dir)
        self.traces_dir = Path(traces_dir)
        self.model_name = model_name
        self.max_workers = max_workers

        self.pgo_exe = Path(__file__).parent / "pgo.jar"
        
        # Ensure base traces directory exists
        self.traces_dir.mkdir(parents=True, exist_ok=True)
        
    def evaluate(self, task_name: str, config: Dict[str, Any], spec_file_path: str, config_file_path: str) -> ConsistencyEvaluationResult:
        """
        Run trace validation evaluation for a given task.

        Args:
            task_name: Name of the task/system (e.g., "etcd", "asterinas")
            config: Configuration parameters for trace generation
            
        Returns:
            ConsistencyEvaluationResult with evaluation results
        """
        result = ConsistencyEvaluationResult(task_name=task_name, method_name="direct_call", model_name=self.model_name)
        result.trace_generation_successful = True # N/A, we store them in repo

        # guess traces location based on spec location (dir tree can be a bit inconsistent)
        traces_out_dir = Path(spec_file_path).parent / "traces_found"
        # This is the original version based on task + model:
        # traces_out_dir = Path(f"data/spec/{task_name}/{self.model_name}/traces_found")

        src_dir = Path(f"tla_eval/core/trace_generation/{task_name}")
        shutil.copytree(src=src_dir / "traces_found", dst=traces_out_dir, dirs_exist_ok=True)
        traces_dirs = [Path(p) for p in Path(traces_out_dir).iterdir() if Path(p).is_dir()]
        if not config_file_path:
            raise ValueError("config_file_path must be provided for PGo trace validation")
        
        result.generated_trace_count = len(traces_dirs)

        convert_start_time = time.time()

        cfg_source_path = Path(config_file_path)
        if cfg_source_path and not cfg_source_path.exists():
            raise FileNotFoundError(f"Config file '{config_file_path}' not found for trace validation")
        spec_source_path = Path(spec_file_path)
        spec_text = spec_source_path.read_text()
        try:
            for traces_dir in traces_dirs:
                subprocess.run([
                    "java", "-jar", self.pgo_exe, "tracegen",
                    src_dir / f"{task_name}.tla",
                    "--noall-paths", traces_dir,
                ], check=True)

                # patch out cfg parts
                cfg_path_tmp = Path(traces_dir) / f"{task_name}Validate.cfg"
                cfg_lines = cfg_path_tmp.read_text().splitlines()
                def cfg_lines_pred(line):
                    if line.startswith("SPECIFICATION"):
                        return line == "SPECIFICATION __Spec"
                    elif line.startswith("INIT "):
                        return False
                    elif line.startswith("NEXT "):
                        return False
                    else:
                        return True
                cfg_lines = filter(cfg_lines_pred, cfg_lines)
                cfg_lines = list(cfg_lines) + (src_dir / f"{task_name}Validate.cfg").read_text().splitlines()
                cfg_path_tmp.write_text('\n'.join(cfg_lines))

                # overwrite TLA+
                (Path(traces_dir) / f"{task_name}.tla").write_text(spec_text)

            refinement_mapping = ""
            if traces_dirs:
                sample_dir = traces_dirs[0]
                refinement_mapping = self._generate_refinement_mapping(
                    task_name,
                    sample_dir / f"{task_name}.tla",
                    sample_dir / f"{task_name}.cfg",
                    sample_dir / f"{task_name}Validate.tla",
                )
                for traces_dir in traces_dirs:
                    self._inject_refinement_mapping(
                        traces_dir / f"{task_name}Validate.tla",
                        refinement_mapping,
                        task_name,
                    )
            result.trace_conversion_time = time.time() - convert_start_time
            result.trace_conversion_successful = True
        except Exception as ex:
            traceback.print_exception(ex)
            result.trace_conversion_successful = False
            result.trace_conversion_error = ex
            result.trace_conversion_time = time.time() - convert_start_time
            return result

        print(f"generated validation setups for {len(traces_dirs)} traces")

        validation_start_time = time.time()
        try:
            task_label_count_map = {
                "dqueue": 6,
                "locksvc": 6,
                "raftkvs": 14,
            }
            
            validate_ok = True
            cov_ok_pcs = set()
            cov_bad_pcs = set()
            for traces_dir in traces_dirs:
                tlc_result = subprocess.run(
                    [
                        "java", "-jar", self.pgo_exe, "tlc",
                        "--dfs", Path(traces_dir) / f"{task_name}Validate.tla",
                    ],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                print(tlc_result.stdout)
                if tlc_result.returncode != 0:
                    validate_ok = False
                    init_frag = "  pc |-> \""
                    end_frag = "\","
                    pcs = [l for l in tlc_result.stdout.splitlines() if l.startswith(init_frag) and l.endswith(end_frag)]
                    if pcs:
                        cov_ok_pcs |= set(pcs[:-1])
                        cov_bad_pcs.add(pcs[-1])

            coverage = len(cov_ok_pcs - cov_bad_pcs)
            total_label_count = task_label_count_map[task_name]
            coverage_percent = coverage / total_label_count * 100
            print(f"Coverage: {coverage} / {total_label_count} -> {coverage_percent}% (ok = {cov_ok_pcs} vs bad = {cov_bad_pcs})")
            result.trace_validation_successful = validate_ok
            result.trace_validation_time = time.time() - validation_start_time
            result.overall_success = validate_ok
        except Exception as ex:
            traceback.print_exception(ex)
            result.trace_validation_successful = False
            result.trace_validation_time = time.time() - validation_start_time

        return result

    def get_evaluation_name(self) -> str:
        """Get the name of this evaluation method."""
        return "pgo_trace_validation"
    
    def get_supported_tasks(self):
        """Get list of tasks supported by this evaluator."""
        return ["dqueue", "locksvc", "raftkvs"]
    
    def get_default_config(self, system_name: str = None) -> Dict[str, Any]:
        return {}
    
    def get_available_scenarios(self, system_name: str = None) -> Dict[str, Dict[str, Any]]:
        """
        Get available predefined scenarios.
        
        Args:
            system_name: Optional system name to get system-specific scenarios
            
        Returns:
            Dictionary mapping scenario names to their configurations
        """
        
        return {}

    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "consistency_pgo_trace_validation"

    def _generate_refinement_mapping(self, task_name: str, spec_path: Path, cfg_path: Path, validate_path: Path) -> str:
        prompt_path = Path("data/tracelink_prompts/prompt.txt")
        prompt_template = prompt_path.read_text()

        spec_contents = self._extract_declaration_lines(spec_path)
        validate_contents = self._extract_declaration_lines(validate_path)
        cfg_contents = cfg_path.read_text() if cfg_path.exists() else ""

        prompt = prompt_template.format(
            spec_file=str(spec_path),
            spec_cfg=str(cfg_path),
            spec_validate_file=str(validate_path),
            spec_file_contents=spec_contents,
            spec_cfg_contents=cfg_contents,
            spec_validate_file_contents=validate_contents,
        )

        model = get_configured_model("claude") # hardcoded based on what works best for other refinement tasks
        generation_config = GenerationConfig()
        result = model.generate_direct(prompt, generation_config)

        if not result.success:
            raise RuntimeError(f"Failed to generate refinement mapping: {result.error_message}")

        mapping_text = result.generated_text.strip()

        if not mapping_text:
            raise RuntimeError("Model returned empty refinement mapping")

        return mapping_text

    def _extract_declaration_lines(self, file_path: Path) -> str:
        if not file_path.exists():
            return ""

        relevant_keywords = {"CONSTANT", "CONSTANTS", "VARIABLE", "VARIABLES"}
        lines: List[str] = []
        for line in file_path.read_text().splitlines():
            stripped = line.strip()
            if not stripped:
                continue
            keyword = stripped.split(maxsplit=1)[0]
            if keyword in relevant_keywords:
                lines.append(line.rstrip())

        return "\n".join(lines)

    def _inject_refinement_mapping(self, validate_path: Path, mapping_text: str, task_name: str) -> None:
        insert_lines = self._prepare_refinement_lines(mapping_text, task_name)
        if not insert_lines:
            return

        lines = validate_path.read_text().splitlines()
        target_line = f"__instance == INSTANCE {task_name}"

        try:
            target_index = next(i for i, line in enumerate(lines) if line.strip() == target_line)
        except StopIteration as exc:
            raise RuntimeError(f"Could not locate '{target_line}' in {validate_path}") from exc

        if lines[target_index + 1: target_index + 1 + len(insert_lines)] == insert_lines:
            return

        updated_lines = lines[: target_index + 1] + insert_lines + lines[target_index + 1 :]
        validate_path.write_text("\n".join(updated_lines) + "\n")

    def _prepare_refinement_lines(self, mapping_text: str, task_name: str) -> List[str]:
        lines = [line.rstrip() for line in mapping_text.splitlines()]

        while lines and not lines[0].strip():
            lines.pop(0)
        while lines and not lines[-1].strip():
            lines.pop()

        instance_line = f"INSTANCE {task_name}"
        for index, line in enumerate(list(lines)):
            if line.strip() == instance_line:
                lines.pop(index)
                break

        target_line = f"__instance == INSTANCE {task_name}"
        cleaned_lines: List[str] = []
        target_removed = False
        for line in lines:
            if not target_removed and line.strip() == target_line:
                target_removed = True
                continue
            cleaned_lines.append(line)

        while cleaned_lines and not cleaned_lines[0].strip():
            cleaned_lines.pop(0)
        while cleaned_lines and not cleaned_lines[-1].strip():
            cleaned_lines.pop()

        return cleaned_lines


# Convenience function for backward compatibility
def create_trace_validation_evaluator(
    spec_dir: str = "data/spec",
    traces_dir: str = "data/sys_traces",
    timeout: int = 600,
    model_name: str = None,
    max_workers: int = 4
) -> PGoTraceValidationEvaluator:
    """
    Factory function to create a trace validation evaluator.
    
    Args:
        spec_dir: Directory containing TLA+ specifications
        traces_dir: Base directory to store generated traces
        timeout: Timeout for evaluation operations in seconds
        model_name: Name of the model to use for specTrace generation
        max_workers: Maximum number of worker threads for concurrent trace validation
        
    Returns:
        TraceValidationEvaluator instance
    """
    return PGoTraceValidationEvaluator(spec_dir, traces_dir, timeout, model_name, max_workers)
