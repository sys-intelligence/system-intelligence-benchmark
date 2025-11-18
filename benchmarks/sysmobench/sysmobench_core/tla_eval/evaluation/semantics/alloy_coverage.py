"""
Alloy Coverage Evaluator: Analyzes signature and field coverage.

This evaluator uses AlloyCoverage to analyze which signatures and fields
are instantiated in the generated instances.
"""

import logging
import os
import subprocess
import time
import json
from pathlib import Path
from typing import Optional, Dict, List

from ...models.base import GenerationResult
from ...utils.output_manager import get_output_manager
from ..base.evaluator import BaseEvaluator
from ..base.result_types import SemanticEvaluationResult

logger = logging.getLogger(__name__)


class AlloyCoverageEvaluator(BaseEvaluator):
    """
    Evaluator for Alloy coverage analysis (signature and field coverage).
    """

    def __init__(self, validation_timeout: int = 60):
        """
        Initialize Alloy coverage evaluator.

        Args:
            validation_timeout: Timeout for coverage analysis in seconds
        """
        super().__init__(timeout=validation_timeout)
        self.alloy_jar = Path("lib/alloy.jar")
        self.coverage_class = "AlloyCoverage"

        if not self.alloy_jar.exists():
            raise FileNotFoundError(f"Alloy JAR not found: {self.alloy_jar}")

    def evaluate(self,
                generation_result: GenerationResult,
                task_name: str,
                method_name: str,
                model_name: str,
                spec_module: str = None,
                spec_file_path: Optional[str] = None,
                config_file_path: Optional[str] = None) -> SemanticEvaluationResult:
        """
        Evaluate Alloy specification coverage.

        Args:
            generation_result: Result from Alloy generation
            task_name: Name of the task
            method_name: Name of the generation method
            model_name: Name of the model used
            spec_module: Not used for Alloy
            spec_file_path: Optional path to existing .als file
            config_file_path: Not used for Alloy

        Returns:
            SemanticEvaluationResult with coverage metrics
        """
        logger.info(f"Evaluating Alloy coverage: {task_name}/{method_name}/{model_name}")

        # Create output directory
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="coverage",
            task=task_name,
            method=method_name,
            model=model_name,
            language="alloy"
        )
        logger.info(f"Using output directory: {output_dir}")

        # Create evaluation result
        eval_result = SemanticEvaluationResult(task_name, method_name, model_name)

        # Get generation time if available
        if generation_result and generation_result.metadata:
            eval_result.generation_time = generation_result.metadata.get('latency_seconds', 0.0)

        # Get Alloy content
        if spec_file_path and Path(spec_file_path).exists():
            logger.info(f"Using existing spec file: {spec_file_path}")
            alloy_file = Path(spec_file_path)
            eval_result.specification_file = str(alloy_file)
        elif generation_result and generation_result.generated_text:
            logger.info("Using generated Alloy specification")
            # Save to output directory
            alloy_file = output_dir / f"{task_name}.als"
            alloy_file.write_text(generation_result.generated_text, encoding='utf-8')
            eval_result.specification_file = str(alloy_file)
        else:
            logger.error("No valid spec file or generation result provided")
            eval_result.model_checking_successful = False
            eval_result.model_checking_error = "No specification provided"
            eval_result.overall_success = False
            return eval_result

        # Execute coverage analysis
        logger.info("Starting Alloy coverage analysis")
        start_time = time.time()

        coverage_result = self._execute_coverage(alloy_file)

        eval_result.model_checking_time = time.time() - start_time

        if coverage_result['success']:
            eval_result.model_checking_successful = True
            eval_result.model_checking_error = None

            # Store coverage metrics in custom_data
            eval_result.custom_data = {
                'instances_found': coverage_result.get('instances_found', 0),
                'total_signatures': coverage_result.get('total_signatures', 0),
                'covered_signatures': coverage_result.get('covered_signatures', 0),
                'signature_coverage_percent': coverage_result.get('signature_coverage_percent', 0.0),
                'total_fields': coverage_result.get('total_fields', 0),
                'covered_fields': coverage_result.get('covered_fields', 0),
                'field_coverage_percent': coverage_result.get('field_coverage_percent', 0.0),
                'covered_signature_list': coverage_result.get('covered_signature_list', []),
                'uncovered_signature_list': coverage_result.get('uncovered_signature_list', []),
                'covered_field_list': coverage_result.get('covered_field_list', []),
                'uncovered_field_list': coverage_result.get('uncovered_field_list', [])
            }

            logger.info(
                f"Coverage analysis complete: "
                f"Sig {coverage_result['covered_signatures']}/{coverage_result['total_signatures']} "
                f"({coverage_result['signature_coverage_percent']:.1f}%), "
                f"Field {coverage_result['covered_fields']}/{coverage_result['total_fields']} "
                f"({coverage_result['field_coverage_percent']:.1f}%)"
            )
        else:
            eval_result.model_checking_successful = False
            eval_result.model_checking_error = coverage_result.get('error', 'Unknown error')
            logger.error(f"Coverage analysis failed: {eval_result.model_checking_error}")

        eval_result.overall_success = eval_result.model_checking_successful

        # Save results
        results_file = output_dir / "evaluation_result.json"
        try:
            with open(results_file, 'w', encoding='utf-8') as f:
                json.dump(eval_result.to_dict(), f, indent=2)
            logger.info(f"Saved evaluation results to {results_file}")
        except Exception as e:
            logger.warning(f"Failed to save results: {e}")

        return eval_result

    def _execute_coverage(self, spec_file: Path) -> Dict:
        """
        Execute Alloy coverage analyzer.

        Args:
            spec_file: Path to .als file

        Returns:
            Dictionary with coverage results
        """
        classpath = os.pathsep.join([
            str(self.alloy_jar),
            str(self.alloy_jar.parent)
        ])

        cmd = [
            "java",
            "-cp", classpath,
            self.coverage_class,
            str(spec_file.resolve()),
            "--timeout", str(self.timeout)
        ]

        logger.info(f"Running: {' '.join(cmd)}")

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.timeout + 10  # Extra buffer
            )

            return self._parse_coverage_output(result.returncode, result.stdout, result.stderr)

        except subprocess.TimeoutExpired:
            logger.error(f"Coverage analysis timeout after {self.timeout}s")
            return {
                'success': False,
                'error': f"Timeout after {self.timeout}s"
            }

        except Exception as e:
            logger.error(f"Failed to run coverage analyzer: {e}")
            return {
                'success': False,
                'error': f"Cannot run coverage analyzer: {e}"
            }

    def _parse_coverage_output(self, returncode: int, stdout: str, stderr: str) -> Dict:
        """
        Parse output from AlloyCoverage.

        Args:
            returncode: Exit code
            stdout: Standard output
            stderr: Standard error

        Returns:
            Dictionary with parsed results
        """
        result = {
            'success': False,
            'instances_found': 0,
            'total_signatures': 0,
            'covered_signatures': 0,
            'signature_coverage_percent': 0.0,
            'total_fields': 0,
            'covered_fields': 0,
            'field_coverage_percent': 0.0,
            'covered_signature_list': [],
            'uncovered_signature_list': [],
            'covered_field_list': [],
            'uncovered_field_list': []
        }

        if returncode == 0:
            # Success - parse coverage data
            lines = stdout.split('\n')
            current_section = None

            for line in lines:
                line = line.strip()

                # Parse summary metrics
                if line.startswith('INSTANCES_FOUND:'):
                    result['instances_found'] = int(line.split(':')[1].strip())
                elif line.startswith('TOTAL_SIGNATURES:'):
                    result['total_signatures'] = int(line.split(':')[1].strip())
                elif line.startswith('COVERED_SIGNATURES:'):
                    parts = line.split(':')[1].strip().split('/')
                    result['covered_signatures'] = int(parts[0])
                elif line.startswith('SIGNATURE_COVERAGE:'):
                    percent_str = line.split(':')[1].strip().replace('%', '')
                    result['signature_coverage_percent'] = float(percent_str)
                elif line.startswith('TOTAL_FIELDS:'):
                    result['total_fields'] = int(line.split(':')[1].strip())
                elif line.startswith('COVERED_FIELDS:'):
                    parts = line.split(':')[1].strip().split('/')
                    result['covered_fields'] = int(parts[0])
                elif line.startswith('FIELD_COVERAGE:'):
                    percent_str = line.split(':')[1].strip().replace('%', '')
                    result['field_coverage_percent'] = float(percent_str)

                # Track sections
                elif line == '=== COVERED_SIGNATURES_LIST ===':
                    current_section = 'covered_sigs'
                elif line == '=== UNCOVERED_SIGNATURES_LIST ===':
                    current_section = 'uncovered_sigs'
                elif line == '=== COVERED_FIELDS_LIST ===':
                    current_section = 'covered_fields'
                elif line == '=== UNCOVERED_FIELDS_LIST ===':
                    current_section = 'uncovered_fields'
                elif line.startswith('==='):
                    current_section = None

                # Parse list items
                elif line.startswith('SIG:') and current_section:
                    sig_name = line.split(':', 1)[1].strip()
                    if current_section == 'covered_sigs':
                        result['covered_signature_list'].append(sig_name)
                    elif current_section == 'uncovered_sigs':
                        result['uncovered_signature_list'].append(sig_name)

                elif line.startswith('FIELD:') and current_section:
                    field_name = line.split(':', 1)[1].strip()
                    if current_section == 'covered_fields':
                        result['covered_field_list'].append(field_name)
                    elif current_section == 'uncovered_fields':
                        result['uncovered_field_list'].append(field_name)

            result['success'] = True
            return result

        elif returncode == 1:
            # No instances found or analysis failed
            error_msg = stderr if stderr else "No instances found for coverage analysis"
            return {
                'success': False,
                'error': error_msg
            }

        else:
            # Internal error
            return {
                'success': False,
                'error': f"Coverage analyzer internal error (code {returncode}): {stderr}"
            }

    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "alloy_coverage"
