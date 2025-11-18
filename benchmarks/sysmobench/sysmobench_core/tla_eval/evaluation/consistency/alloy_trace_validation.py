"""
Alloy Trace Validation Evaluator

This evaluator implements trace validation for Alloy specifications by:
1. Reusing TLA+ trace generation infrastructure
2. Converting traces to Alloy facts
3. Merging base specs with trace facts
4. Running Alloy verification (SAT/UNSAT checking)
"""

import json
import logging
import os
import subprocess
import time
from pathlib import Path
from typing import Dict, List, Any
from concurrent.futures import ThreadPoolExecutor, as_completed

from ...core.trace_generation.registry import get_system
from ...core.spec_processing.alloy_trace_processor import AlloyTraceConverter
from ...core.verification.alloy_validator import AlloyValidator
from ..base.evaluator import BaseEvaluator
from ..base.result_types import ConsistencyEvaluationResult
from ...utils.output_manager import get_output_manager

logger = logging.getLogger(__name__)


class AlloyTraceValidationEvaluator(BaseEvaluator):
    """Alloy Trace Validation Evaluator"""

    def __init__(self,
                 timeout: int = 600,
                 max_workers: int = 4,
                 with_exist_traces: int = None,
                 alloy_jar_path: str = "lib/alloy.jar"):
        """
        Initialize the evaluator.

        Args:
            timeout: Validation timeout in seconds
            max_workers: Maximum number of concurrent validation workers
            with_exist_traces: Number of pre-generated trace files to reuse (None ⇒ generate new ones)
            alloy_jar_path: Path to the Alloy JAR
        """
        super().__init__(timeout=timeout)
        self.max_workers = max_workers
        self.with_exist_traces = with_exist_traces
        self.validator = AlloyValidator(timeout=timeout)
        self.alloy_jar = Path(alloy_jar_path)
        self.runtime_class = "AlloyRuntime"

    def evaluate(self, task_name: str, config: Dict[str, Any],
                spec_file_path: str = None,
                config_file_path: str = None) -> ConsistencyEvaluationResult:
        """
        Execute Alloy trace validation.

        Args:
            task_name: Task identifier (e.g., "spin")
            config: Evaluation configuration
            spec_file_path: Optional path to the base Alloy spec
            config_file_path: Reserved for parity with other evaluators (unused)

        Returns:
            ConsistencyEvaluationResult
        """
        logger.info(f"Starting Alloy trace validation for task: {task_name}")

        # Create the output directory
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="trace_validation",
            task=task_name,
            method="alloy",
            model="trace_gen",
            language="alloy"
        )
        logger.info(f"Output directory: {output_dir}")

        # Initialize the result container
        result = ConsistencyEvaluationResult(task_name, "trace_validation", "alloy")

        try:
            # Step 1: Generate or load system traces (reuse the TLA+ infrastructure)
            logger.info("Step 1: Loading/generating system traces...")
            trace_files = self._get_trace_files(task_name, config, output_dir)

            if not trace_files:
                result.trace_generation_error = "No traces available"
                return result

            result.trace_generation_successful = True
            result.raw_trace_files = trace_files
            logger.info(f"Step 1 complete: {len(trace_files)} traces ready")

            # Step 2: Convert traces → Alloy facts
            logger.info("Step 2: Converting traces to Alloy facts...")
            fact_files = self._convert_traces_to_facts(
                task_name, trace_files, output_dir
            )

            if not fact_files:
                result.trace_conversion_error = "Failed to convert traces to facts"
                return result

            result.trace_conversion_successful = True
            logger.info(f"Step 2 complete: {len(fact_files)} fact files generated")

            # Step 3: Merge the base spec with the fact blocks
            logger.info("Step 3: Merging base spec with facts...")
            validation_specs = self._merge_specs_and_facts(
                task_name, spec_file_path, fact_files, output_dir
            )

            if not validation_specs:
                result.trace_conversion_error = "Failed to merge specs and facts"
                return result

            logger.info(f"Step 3 complete: {len(validation_specs)} validation specs created")

            # Step 4: Run Alloy validations concurrently
            logger.info(f"Step 4: Running Alloy validation ({self.max_workers} workers)...")
            validation_results = self._run_concurrent_validation(validation_specs)

            # Aggregate outcomes
            successful = sum(1 for r in validation_results if r['success'])
            total = len(validation_results)
            success_rate = (successful / total * 100) if total > 0 else 0

            result.trace_validation_successful = (successful == total)
            result.validated_events = sum(r.get('num_events', 0) for r in validation_results)
            result.custom_data = {
                'total_traces': total,
                'successful_traces': successful,
                'failed_traces': total - successful,
                'success_rate': success_rate,
                'validation_results': validation_results
            }

            logger.info(f"Step 4 complete: {successful}/{total} traces validated ({success_rate:.1f}%)")

            # Persist the evaluation summary
            self._save_results(result, output_dir)

            return result

        except Exception as e:
            logger.error(f"Alloy trace validation failed: {e}", exc_info=True)
            result.trace_validation_error = str(e)
            return result

    def _get_trace_files(self, task_name: str, config: Dict,
                        output_dir: Path) -> List[Path]:
        """Load existing traces or generate new ones."""
        if self.with_exist_traces:
            # Load pre-generated traces
            traces_dir = Path(f"data/sys_traces/{task_name}")
            trace_files = sorted(traces_dir.glob("trace_*.jsonl"))[:self.with_exist_traces]
            logger.info(f"Loaded {len(trace_files)} existing traces from {traces_dir}")
            return trace_files
        else:
            # Generate fresh traces (reuse the TLA+ implementation)
            system_module = get_system(task_name)
            num_traces = config.get('num_traces', 10)

            logger.info(f"Generating {num_traces} new traces using system module...")
            trace_generator = system_module.get_trace_generator()

            # Produce traces via the system generator
            trace_results = trace_generator.generate_traces(
                config=config,
                output_dir=Path(f"data/sys_traces/{task_name}"),
                name_prefix=f"{task_name}_trace"
            )

            # Collect the successful trace files
            trace_files = [
                Path(tr['trace_file'])
                for tr in trace_results
                if tr['success']
            ]

            logger.info(f"Generated {len(trace_files)} traces successfully")
            return trace_files

    def _convert_traces_to_facts(self, task_name: str,
                                 trace_files: List[Path],
                                 output_dir: Path) -> List[Path]:
        """Convert every trace into an Alloy fact file."""
        converter = AlloyTraceConverter(task_name)
        fact_files = []

        for i, trace_file in enumerate(trace_files):
            logger.info(f"Converting trace {i+1}/{len(trace_files)}: {trace_file.name}")

            try:
                # Trace → facts
                facts_content = converter.convert_trace_file(trace_file)

                # Persist the facts
                fact_file = output_dir / f"trace_{i+1:02d}.facts"
                fact_file.write_text(facts_content, encoding='utf-8')
                fact_files.append(fact_file)

                logger.info(f"Generated facts file: {fact_file.name}")

            except Exception as e:
                logger.error(f"Failed to convert {trace_file}: {e}", exc_info=True)
                continue

        return fact_files

    def _merge_specs_and_facts(self, task_name: str,
                               base_spec_path: str,
                               fact_files: List[Path],
                               output_dir: Path) -> List[Path]:
        """Merge the base spec with every fact file."""
        # Read the base spec
        if base_spec_path:
            base_spec_file = Path(base_spec_path)
            if not base_spec_file.exists():
                raise FileNotFoundError(f"Base spec not found: {base_spec_path}")
            base_spec = base_spec_file.read_text(encoding='utf-8')
            logger.info(f"Using user-specified base spec: {base_spec_path}")
        else:
            # Discover generated specs inside output_dir or fallback paths
            possible_paths = [
                output_dir / f"{task_name}.als",
                Path(f"data/spec/{task_name}/{task_name}.als"),
                Path(f"output/spec_generation/{task_name}/*/generated/{task_name}.als")
            ]

            base_spec_file = None
            for path_pattern in possible_paths:
                if '*' in str(path_pattern):
                    # Glob pattern
                    matches = list(Path('.').glob(str(path_pattern)))
                    if matches:
                        base_spec_file = matches[0]
                        break
                else:
                    if path_pattern.exists():
                        base_spec_file = path_pattern
                        break

            if not base_spec_file:
                raise FileNotFoundError(
                    f"Base spec not found for task {task_name}. "
                    f"Please specify spec_file_path or ensure spec exists in default locations."
                )

            base_spec = base_spec_file.read_text(encoding='utf-8')
            logger.info(f"Using base spec from: {base_spec_file}")

        # Extract original run expression and scope to reuse later
        run_expression = self._extract_run_expression(base_spec)
        # Extract scope parameters from the base spec
        scope_params = self._extract_scope_from_spec(base_spec)
        logger.info(f"Extracted scope parameters: {scope_params}")

        validation_specs = []

        for i, fact_file in enumerate(fact_files):
            # Read the fact block
            facts = fact_file.read_text(encoding='utf-8')

            # Determine #Time from the facts, falling back to base spec scope
            import re
            time_match = re.search(r'#Time\s*=\s*(\d+)', facts)
            num_time = int(time_match.group(1)) if time_match else scope_params.get('Time', 10)

            # Merge spec + facts
            merged_spec = self._merge_content(
                base_spec, facts, i+1,
                num_time=num_time,
                num_threads=scope_params.get('Thread', 2),
                num_locks=scope_params.get('Lock', 1),
                run_expression=run_expression
            )

            # Save the merged spec
            output_file = output_dir / f"{task_name}_trace_{i+1:02d}.als"
            output_file.write_text(merged_spec, encoding='utf-8')
            validation_specs.append(output_file)

            logger.info(f"Created validation spec: {output_file.name}")

        return validation_specs

    def _extract_scope_from_spec(self, base_spec: str) -> Dict[str, int]:
        """Parse scope parameters from the base spec."""
        import re

        # Look for run commands such as: run Foo for 10 Time, 2 Thread, 1 Lock
        run_match = re.search(r'run\s+(?:\{[^}]*\}|[^{\s]+)\s+for\s+(.+)', base_spec, flags=re.IGNORECASE | re.DOTALL)

        scope_params = {}
        if run_match:
            scope_str = run_match.group(1)
            # Parse segments like "10 Time, 2 Thread, 1 Lock"
            for part in scope_str.split(','):
                part = part.strip()
                match = re.match(r'(\d+)\s+(\w+)', part)
                if match:
                    count, sig_name = match.groups()
                    scope_params[sig_name] = int(count)

        # Provide defaults when the spec omits scopes
        scope_params.setdefault('Time', 10)
        scope_params.setdefault('Thread', 2)
        scope_params.setdefault('Lock', 1)

        return scope_params

    def _merge_content(self, base_spec: str, facts: str, trace_num: int,
                      num_time: int, num_threads: int, num_locks: int,
                      run_expression: str = None) -> str:
        """Combine the base spec and facts into a runnable Alloy module."""
        base_spec_without_run = self._remove_run_commands(base_spec)

        if not run_expression:
            run_expression = "InitSpec"
        run_expression = run_expression.strip()

        return f"""{base_spec_without_run}

// ===== TRACE VALIDATION FACTS (Trace {trace_num}) =====
{facts}

// ===== TRACE CONFORMANCE COMMAND =====
run {run_expression} for exactly {num_time} Time, {num_threads} Thread, {num_locks} Lock
"""

    def _extract_run_expression(self, spec_content: str) -> str:
        """Extract the original run command expression."""
        if not spec_content:
            return None

        import re
        match = re.search(r'run\s+(.+?)(?:\s+for\b|$)', spec_content, flags=re.IGNORECASE | re.DOTALL)
        if match:
            expression = match.group(1).strip()
            return expression if expression else None
        return None

    def _remove_run_commands(self, spec_content: str) -> str:
        """Remove all run commands (with or without braces) from the spec."""
        cleaned_lines = []
        skip_block = False
        brace_balance = 0

        for line in spec_content.splitlines():
            stripped = line.lstrip().lower()
            if stripped.startswith("run "):
                brace_balance = line.count("{") - line.count("}")
                skip_block = brace_balance > 0
                continue

            if skip_block:
                brace_balance += line.count("{") - line.count("}")
                if brace_balance <= 0:
                    skip_block = False
                continue

            cleaned_lines.append(line)

        return "\n".join(cleaned_lines)

    def _run_concurrent_validation(self, validation_specs: List[Path]) -> List[Dict]:
        """Validate all merged specs in parallel."""
        results = []

        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            future_to_spec = {
                executor.submit(self._validate_single_spec, spec): spec
                for spec in validation_specs
            }

            for future in as_completed(future_to_spec):
                spec = future_to_spec[future]
                try:
                    result = future.result()
                    results.append(result)
                except Exception as e:
                    logger.error(f"Validation failed for {spec}: {e}", exc_info=True)
                    results.append({
                        'spec_file': str(spec),
                        'success': False,
                        'error': str(e)
                    })

        return results

    def _validate_single_spec(self, spec_path: Path) -> Dict:
        """Validate a single merged spec."""
        logger.info(f"Validating: {spec_path.name}")

        start_time = time.time()

        # Execute the Alloy runtime to run the command
        runtime_result = self._run_alloy_runtime(spec_path)

        execution_time = time.time() - start_time

        # Parse the output to determine SAT/UNSAT
        success = runtime_result['success'] and runtime_result.get('satisfiable', False)

        validation_result = {
            'spec_file': str(spec_path),
            'success': success,
            'execution_time': execution_time,
            'output': runtime_result.get('output', ''),
            'num_events': self._extract_num_events(spec_path)
        }

        if success:
            logger.info(f"✓ Validation passed: {spec_path.name} ({execution_time:.2f}s)")
        else:
            logger.warning(f"✗ Validation failed: {spec_path.name} ({execution_time:.2f}s)")
            if 'error' in runtime_result:
                validation_result['error'] = runtime_result['error']

        return validation_result

    def _extract_num_events(self, spec_path: Path) -> int:
        """Extract the number of events encoded in the spec."""
        content = spec_path.read_text(encoding='utf-8')
        # Look for #Time = N markers
        import re
        match = re.search(r'#Time\s*=\s*(\d+)', content)
        return int(match.group(1)) if match else 0

    def _save_results(self, result: ConsistencyEvaluationResult, output_dir: Path):
        """Write the aggregated result JSON to disk."""
        results_file = output_dir / "validation_results.json"
        with open(results_file, 'w', encoding='utf-8') as f:
            json.dump(result.to_dict(), f, indent=2, ensure_ascii=False)
        logger.info(f"Results saved to: {results_file}")

    def get_default_config(self, task_name: str = None) -> Dict[str, Any]:
        """Return default configuration for Alloy trace validation."""
        if task_name and is_system_supported(task_name):
            system_module = get_system(task_name)
            if system_module:
                trace_generator = system_module.get_trace_generator()
                if hasattr(trace_generator, "get_default_config"):
                    return trace_generator.get_default_config()

        return {
            "num_traces": 5,
            "scenario": "normal_operation"
        }

    def _get_evaluation_type(self) -> str:
        return "alloy_trace_validation"

    def _run_alloy_runtime(self, spec_file: Path) -> Dict:
        """
        Invoke the AlloyRuntime helper to execute run/check commands.

        Args:
            spec_file: Path to the Alloy module

        Returns:
            Dictionary describing the execution result
        """
        # Build classpath
        classpath = os.pathsep.join([
            str(self.alloy_jar),
            str(self.alloy_jar.parent)
        ])

        cmd = [
            "java",
            "-cp", classpath,
            self.runtime_class,
            str(spec_file.resolve()),
            "--timeout", str(self.timeout)
        ]

        logger.debug(f"Running: {' '.join(cmd)}")

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.timeout + 10  # Add buffer
            )

            # Parse output
            return self._parse_alloy_runtime_output(result.returncode, result.stdout, result.stderr)

        except subprocess.TimeoutExpired:
            logger.error(f"Alloy runtime timeout after {self.timeout}s")
            return {
                'success': False,
                'satisfiable': False,
                'output': f"Timeout after {self.timeout}s",
                'error': f"Timeout after {self.timeout}s"
            }

        except Exception as e:
            logger.error(f"Failed to run Alloy runtime: {e}", exc_info=True)
            return {
                'success': False,
                'satisfiable': False,
                'output': str(e),
                'error': str(e)
            }

    def _parse_alloy_runtime_output(self, returncode: int, stdout: str, stderr: str) -> Dict:
        """
        Parse the AlloyRuntime output.

        Args:
            returncode: Process exit code
            stdout: Standard output
            stderr: Standard error

        Returns:
            Parsed result dictionary
        """
        if returncode == 0:
            # Success - check for SAT/UNSAT
            satisfiable = False

            for line in stdout.split('\n'):
                line = line.strip()
                if line.startswith('STATUS:'):
                    status = line.split(':', 1)[1].strip()
                    if status == 'SATISFIABLE':
                        satisfiable = True
                        break

            return {
                'success': True,
                'satisfiable': satisfiable,
                'output': stdout
            }

        elif returncode == 1:
            # Execution failed
            error_msg = None
            for line in stderr.split('\n'):
                if line.startswith('ERROR_MSG:'):
                    error_msg = line.split(':', 1)[1].strip()

            return {
                'success': False,
                'satisfiable': False,
                'output': stderr,
                'error': error_msg or stderr
            }

        else:
            # Internal error
            return {
                'success': False,
                'satisfiable': False,
                'output': stderr,
                'error': f"Internal error (code {returncode}): {stderr}"
            }


# Convenience function
def create_alloy_trace_validation_evaluator(
    timeout: int = 600,
    max_workers: int = 4,
    with_exist_traces: int = None
) -> AlloyTraceValidationEvaluator:
    """Factory function to create an Alloy trace validation evaluator."""
    return AlloyTraceValidationEvaluator(
        timeout=timeout,
        max_workers=max_workers,
        with_exist_traces=with_exist_traces
    )
