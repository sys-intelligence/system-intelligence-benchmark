"""
Coverage Evaluator: Semantic-level evaluation for TLA+ specification coverage.

This evaluator analyzes the coverage characteristics of generated TLA+
specifications using TLC's built-in coverage statistics. It extracts
comprehensive coverage data including:
1. Variable coverage - how many distinct values each variable takes
2. Action coverage - how many times each action is evaluated and produces new states
3. Expression coverage - how many times each sub-expression is evaluated
4. Cost coverage - allocation costs for expressions that create data structures

The evaluator can work with:
- Just a GenerationResult (creates both .tla and .cfg files)
- Existing .tla and .cfg files (reuses them)
- .tla file with generated .cfg file
"""

import os
import re
import tempfile
import shutil
import logging
import time
import subprocess
from pathlib import Path
from typing import Dict, List, Any, Tuple, Optional, Set
from dataclasses import dataclass, field

from ...models.base import GenerationResult
from ...utils.output_manager import get_output_manager
from .runtime_check import ConfigGenerator
from ..base.evaluator import BaseEvaluator
from ..base.result_types import SemanticEvaluationResult
from .runtime_check import TLCRunner  # Reuse TLC runner

logger = logging.getLogger(__name__)


@dataclass
class CoverageData:
    """Comprehensive coverage data extracted from TLC coverage statistics"""
    
    # Variable coverage: variable_name -> distinct_value_count
    variable_coverage: Dict[str, int] = field(default_factory=dict)
    
    # Action coverage: action_name -> (evaluations, new_states)
    action_coverage: Dict[str, Tuple[int, int]] = field(default_factory=dict)
    
    # State-level expression coverage: expression -> (evaluations, new_states)
    init_coverage: Dict[str, Tuple[int, int]] = field(default_factory=dict)
    
    # Sub-expression coverage: expression -> evaluations
    expression_coverage: Dict[str, int] = field(default_factory=dict)
    
    # Cost coverage: expression -> (evaluations, cost)
    cost_coverage: Dict[str, Tuple[int, int]] = field(default_factory=dict)
    
    # Property/constraint coverage
    property_coverage: Dict[str, Any] = field(default_factory=dict)
    constraint_coverage: Dict[str, Tuple[int, int]] = field(default_factory=dict)
    
    # Summary statistics
    total_expressions: int = 0
    covered_expressions: int = 0
    total_variables: int = 0
    total_actions: int = 0
    successful_actions: int = 0
    total_evaluations: int = 0
    total_cost: int = 0


@dataclass
class LocationInfo:
    """TLA+ source location information"""
    start_line: int
    start_col: int
    end_line: int
    end_col: int
    module: str
    
    @classmethod
    def parse(cls, location_str: str) -> 'LocationInfo':
        """Parse location string like 'line 4, col 11 to line 4, col 11 of module TestCoverage'"""
        # line 4, col 11 to line 4, col 11 of module TestCoverage
        pattern = r'line (\d+), col (\d+) to line (\d+), col (\d+) of module (\w+)'
        match = re.match(pattern, location_str)
        if match:
            return cls(
                start_line=int(match.group(1)),
                start_col=int(match.group(2)),
                end_line=int(match.group(3)),
                end_col=int(match.group(4)),
                module=match.group(5)
            )
        raise ValueError(f"Cannot parse location string: {location_str}")


class TLCCoverageParser:
    """Parser for TLC tool mode coverage output"""
    
    # TLC message codes for coverage statistics
    MESSAGE_CODES = {
        2201: "coverage_start",      # TLC_COVERAGE_START
        2202: "coverage_end",        # TLC_COVERAGE_END
        2221: "expression_value",    # TLC_COVERAGE_VALUE
        2775: "expression_cost",     # TLC_COVERAGE_VALUE_COST  
        2779: "variable_coverage",   # TLC_COVERAGE_VAR
        2773: "init_coverage",       # TLC_COVERAGE_INIT
        2772: "action_coverage",     # TLC_COVERAGE_NEXT
        2778: "constraint_coverage", # TLC_COVERAGE_CONSTRAINT
        2774: "property_coverage"    # TLC_COVERAGE_PROPERTY
    }
    
    def parse_tool_output(self, output: str) -> CoverageData:
        """Parse TLC -tool mode output and extract coverage data"""
        lines = output.split('\n')
        coverage_data = CoverageData()
        
        # Find the last complete coverage section
        last_coverage_start = -1
        last_coverage_end = -1
        
        # First pass: find all coverage section boundaries
        for i, line in enumerate(lines):
            if '@!@!@STARTMSG ' in line:
                msg_code = self._extract_message_code(line)
                if msg_code == 2201:  # Coverage start
                    last_coverage_start = i
                elif msg_code == 2202:  # Coverage end
                    if last_coverage_start != -1:  # Only update if we have a start
                        last_coverage_end = i
        
        # Determine the range to parse
        if last_coverage_start == -1:
            logger.warning("No coverage data found in TLC output")
            return coverage_data
        
        start_idx = last_coverage_start
        if last_coverage_end > last_coverage_start:
            # Complete coverage section found
            end_idx = last_coverage_end + 1
            logger.info(f"Parsing last complete coverage section (lines {start_idx}-{last_coverage_end})")
        else:
            # Incomplete section (likely timeout), parse to end
            end_idx = len(lines)
            logger.info(f"Parsing incomplete coverage section from line {start_idx} to end (likely timeout)")
        
        # Second pass: parse only the last coverage section
        in_coverage_section = False
        for i in range(start_idx, end_idx):
            line = lines[i].strip()
            
            # Check for message start marker
            if '@!@!@STARTMSG ' in line:
                msg_code = self._extract_message_code(line)
                
                if msg_code == 2201:  # Coverage start
                    in_coverage_section = True
                    logger.debug("Started parsing last TLC coverage statistics")
                elif msg_code == 2202:  # Coverage end
                    in_coverage_section = False
                    logger.debug("Finished parsing last TLC coverage statistics")
                    break
                elif in_coverage_section and msg_code in self.MESSAGE_CODES:
                    # Read next line for actual content
                    if i + 1 < len(lines):
                        content = lines[i + 1].strip()
                        self._parse_coverage_line(msg_code, content, coverage_data)
        
        # Calculate summary statistics
        self._calculate_summary(coverage_data)
        
        return coverage_data
    
    def _extract_message_code(self, line: str) -> int:
        """Extract message code from TLC tool output line"""
        # @!@!@STARTMSG 2779:0 @!@!@
        match = re.search(r'@!@!@STARTMSG (\d+):', line)
        return int(match.group(1)) if match else 0
    
    def _parse_coverage_line(self, msg_code: int, content: str, coverage_data: CoverageData):
        """Parse a single coverage line based on message code"""
        try:
            if msg_code == 2779:  # Variable coverage
                self._parse_variable_coverage(content, coverage_data)
            elif msg_code == 2773:  # Init coverage (state-level)
                self._parse_init_coverage(content, coverage_data)
            elif msg_code == 2772:  # Action coverage (next-level)
                self._parse_action_coverage(content, coverage_data)
            elif msg_code == 2778:  # Constraint coverage
                self._parse_constraint_coverage(content, coverage_data)
            elif msg_code == 2774:  # Property coverage
                self._parse_property_coverage(content, coverage_data)
            elif msg_code == 2221:  # Expression value
                self._parse_expression_coverage(content, coverage_data)
            elif msg_code == 2775:  # Expression with cost
                self._parse_cost_coverage(content, coverage_data)
        except Exception as e:
            logger.warning(f"Failed to parse coverage line (code {msg_code}): {content} - {e}")
    
    def _parse_variable_coverage(self, content: str, coverage_data: CoverageData):
        """Parse variable coverage: <x line 4, col 11 to line 4, col 11 of module TestCoverage>: 5"""
        # <x line 4, col 11 to line 4, col 11 of module TestCoverage>: 5
        pattern = r'<(\w+) (.+?)>: (\d+)'
        match = re.match(pattern, content)
        if match:
            var_name = match.group(1)
            location_str = match.group(2)
            distinct_values = int(match.group(3))
            
            coverage_data.variable_coverage[var_name] = distinct_values
            coverage_data.total_variables += 1
            
            logger.debug(f"Variable coverage: {var_name} = {distinct_values} distinct values")
    
    def _parse_init_coverage(self, content: str, coverage_data: CoverageData):
        """Parse init coverage: <Init line 6, col 1 to line 6, col 4 of module TestCoverage>: 1:1"""
        # <Init line 6, col 1 to line 6, col 4 of module TestCoverage>: 1:1
        pattern = r'<(\w+) (.+?)>: (\d+):(\d+)'
        match = re.match(pattern, content)
        if match:
            init_name = match.group(1)
            location_str = match.group(2)
            evaluations = int(match.group(3))
            new_states = int(match.group(4))
            
            coverage_data.init_coverage[init_name] = (evaluations, new_states)
            
            logger.debug(f"Init coverage: {init_name} = {evaluations} evals, {new_states} new states")
    
    def _parse_action_coverage(self, content: str, coverage_data: CoverageData):
        """Parse action coverage: <Inc line 9, col 1 to line 9, col 3 of module TestCoverage>: 5:5"""
        # <Inc line 9, col 1 to line 9, col 3 of module TestCoverage>: 5:5
        pattern = r'<(\w+) (.+?)>: (\d+):(\d+)'
        match = re.match(pattern, content)
        if match:
            action_name = match.group(1)
            location_str = match.group(2)
            evaluations = int(match.group(3))
            new_states = int(match.group(4))
            
            # Only count if this is a new action
            if action_name not in coverage_data.action_coverage:
                coverage_data.total_actions += 1
                if new_states > 0:
                    coverage_data.successful_actions += 1
            else:
                # Update successful actions count if this action now has new states
                old_new_states = coverage_data.action_coverage[action_name][1]
                if old_new_states == 0 and new_states > 0:
                    coverage_data.successful_actions += 1
            
            coverage_data.action_coverage[action_name] = (evaluations, new_states)
            
            logger.debug(f"Action coverage: {action_name} = {evaluations} evals, {new_states} new states")
    
    def _parse_constraint_coverage(self, content: str, coverage_data: CoverageData):
        """Parse constraint coverage: similar to action coverage"""
        pattern = r'<(\w+) (.+?)>: (\d+):(\d+)'
        match = re.match(pattern, content)
        if match:
            constraint_name = match.group(1)
            evaluations = int(match.group(3))
            new_states = int(match.group(4))
            
            coverage_data.constraint_coverage[constraint_name] = (evaluations, new_states)
            
            logger.debug(f"Constraint coverage: {constraint_name} = {evaluations} evals, {new_states} new states")
    
    def _parse_property_coverage(self, content: str, coverage_data: CoverageData):
        """Parse property coverage"""
        # Property coverage format may vary, store as-is for now
        coverage_data.property_coverage[content] = True
        logger.debug(f"Property coverage: {content}")
    
    def _parse_expression_coverage(self, content: str, coverage_data: CoverageData):
        """Parse expression coverage: line 7, col 5 to line 7, col 12 of module TestCoverage: 1"""
        # line 7, col 5 to line 7, col 12 of module TestCoverage: 1
        # |line 10, col 8 to line 10, col 8 of module TestCoverage: 6
        pattern = r'(\|*)(.+?): (\d+)'
        match = re.match(pattern, content)
        if match:
            depth_markers = match.group(1)  # | indicates nesting depth
            location_str = match.group(2)
            evaluations = int(match.group(3))
            
            # Use depth and location as key
            key = f"{len(depth_markers)}:{location_str}"
            
            # Only count if this is a new expression
            if key not in coverage_data.expression_coverage:
                coverage_data.total_expressions += 1
                coverage_data.covered_expressions += 1
            
            coverage_data.expression_coverage[key] = evaluations
            coverage_data.total_evaluations += evaluations
            
            logger.debug(f"Expression coverage: {key} = {evaluations} evals")
    
    def _parse_cost_coverage(self, content: str, coverage_data: CoverageData):
        """Parse cost coverage: ||line 11, col 22 to line 11, col 41 of module TestCosts: 15:24"""
        # ||line 11, col 22 to line 11, col 41 of module TestCosts: 15:24
        pattern = r'(\|*)(.+?): (\d+):(\d+)'
        match = re.match(pattern, content)
        if match:
            depth_markers = match.group(1)
            location_str = match.group(2)
            evaluations = int(match.group(3))
            cost = int(match.group(4))
            
            key = f"{len(depth_markers)}:{location_str}"
            coverage_data.cost_coverage[key] = (evaluations, cost)
            coverage_data.total_cost += cost
            
            logger.debug(f"Cost coverage: {key} = {evaluations} evals, {cost} cost")
    
    def _calculate_summary(self, coverage_data: CoverageData):
        """Calculate summary statistics from parsed coverage data"""
        # Already calculated during parsing
        logger.info(f"Coverage summary: {coverage_data.total_variables} vars, "
                   f"{coverage_data.total_actions} actions ({coverage_data.successful_actions} successful), "
                   f"{coverage_data.covered_expressions} expressions, "
                   f"{coverage_data.total_evaluations} total evaluations, "
                   f"{coverage_data.total_cost} total cost")


class CoverageEvaluator(BaseEvaluator):
    """
    Evaluator for TLA+ specification coverage analysis using TLC coverage statistics.
    
    This evaluator runs TLC with coverage enabled and analyzes the resulting
    coverage data to assess how well the generated specification exercises
    different parts of the state space and specification logic.
    
    Can work with:
    - GenerationResult: creates .tla and .cfg files
    - Existing .tla/.cfg files: reuses them
    - .tla file: generates .cfg file
    """
    
    def __init__(self, 
                 tlc_timeout: int = 120,
                 coverage_interval: int = 1):
        """
        Initialize coverage evaluator.
        
        Args:
            tlc_timeout: Timeout for TLC model checking in seconds
            coverage_interval: Interval for coverage statistics collection in minutes
        """
        super().__init__(timeout=tlc_timeout)
        self.tlc_timeout = tlc_timeout
        self.coverage_interval = coverage_interval
        self.tlc_runner = TLCRunner(timeout=tlc_timeout)  # Reuse existing TLC runner
        self.parser = TLCCoverageParser()
    
    def evaluate(self, 
                generation_result: GenerationResult,
                task_name: str,
                method_name: str,
                model_name: str,
                spec_module: str = None,
                spec_file_path: str = None,
                config_file_path: str = None) -> SemanticEvaluationResult:
        """
        Evaluate coverage of a TLA+ specification.
        
        This method can work in several modes:
        1. With GenerationResult only: creates both .tla and .cfg files
        2. With existing .tla/.cfg files: reuses them for coverage analysis
        3. With .tla file: generates a basic .cfg file
        
        Args:
            generation_result: Result from TLA+ generation (can be None if files provided)
            task_name: Name of the task
            method_name: Name of the generation method
            model_name: Name of the language model
            spec_module: Optional specification module name
            spec_file_path: Optional path to existing .tla file
            config_file_path: Optional path to existing .cfg file
            
        Returns:
            SemanticEvaluationResult: Coverage evaluation results
        """
        logger.info(f"Coverage evaluation: {task_name}/{method_name}/{model_name}")
        
        # Create structured output directory
        output_manager = get_output_manager()
        output_dir = output_manager.create_experiment_dir(
            metric="coverage",
            task=task_name,
            method=method_name,
            model=model_name
        )
        logger.info(f"Using output directory: {output_dir}")
        
        # Create evaluation result
        result = SemanticEvaluationResult(task_name, method_name, model_name)
        
        # Set generation time from the generation result metadata
        if generation_result and hasattr(generation_result, 'metadata') and 'latency_seconds' in generation_result.metadata:
            result.generation_time = generation_result.metadata['latency_seconds']
        
        try:
            # Step 1: Get or create specification files
            if spec_file_path and config_file_path:
                # Mode 1: Use existing .tla and .cfg files (composite mode)
                logger.info(f"✓ Composite mode: Using existing .tla and .cfg files from runtime check")
                logger.info(f"  Source spec: {spec_file_path}")
                logger.info(f"  Source config: {config_file_path}")
                
                # Copy files to coverage output directory for consistency and debugging
                spec_name = Path(spec_file_path).stem
                final_spec_path = output_dir / f"{spec_name}.tla"
                final_config_path = output_dir / f"{spec_name}.cfg"
                
                # Copy spec file
                with open(spec_file_path, 'r', encoding='utf-8') as src:
                    spec_content = src.read()
                with open(final_spec_path, 'w', encoding='utf-8') as dst:
                    dst.write(spec_content)
                
                # Copy config file
                with open(config_file_path, 'r', encoding='utf-8') as src:
                    config_content = src.read()
                with open(final_config_path, 'w', encoding='utf-8') as dst:
                    dst.write(config_content)
                
                logger.info(f"✓ Copied files to coverage output directory:")
                logger.info(f"  Target spec: {final_spec_path}")
                logger.info(f"  Target config: {final_config_path}")
                
                # Convert back to string paths for TLC execution
                final_spec_path = str(final_spec_path)
                final_config_path = str(final_config_path)
                
            elif spec_file_path:
                # Mode 2: Use existing .tla file, generate .cfg file
                logger.info("✓ Using existing .tla file, generating .cfg file")
                final_spec_path = spec_file_path
                
                # Generate basic config file
                final_config_path = self._generate_basic_config_file(spec_file_path, output_dir, task_name, model_name)
                
            else:
                # Mode 3: Create both files from GenerationResult
                if not generation_result or not generation_result.success:
                    logger.error("Generation failed, cannot perform coverage evaluation")
                    result.error_message = "Generation failed"
                    return result
                
                tla_content = generation_result.generated_text
                if not tla_content.strip():
                    logger.error("Empty TLA+ specification from generation result")
                    result.error_message = "Empty specification"
                    return result
                
                logger.info("✓ Creating .tla and .cfg files from GenerationResult")
                
                # Save specification file
                module_name = spec_module or task_name
                final_spec_path = output_dir / f"{module_name}.tla"
                with open(final_spec_path, 'w', encoding='utf-8') as f:
                    f.write(tla_content)
                
                # Generate basic config file
                final_config_path = self._generate_basic_config_file(str(final_spec_path), output_dir, task_name, model_name)
            
            result.specification_file = str(final_spec_path)
            
            # Step 2: Run TLC with coverage enabled
            logger.info("Running TLC with coverage statistics enabled")
            start_time = time.time()
            
            coverage_data = self._run_tlc_with_coverage(
                str(final_spec_path), 
                str(final_config_path),
                output_dir
            )
            
            result.model_checking_time = time.time() - start_time
            
            # Step 3: Store coverage results
            logger.info("Processing coverage data")
            
            # Always consider coverage collection as successful if we got data
            result.overall_success = (
                coverage_data.total_expressions > 0 or 
                coverage_data.total_actions > 0 or 
                coverage_data.total_variables > 0
            )
            
            # Store raw coverage results without scoring
            result.states_explored = coverage_data.total_evaluations
            result.custom_data = {
                'coverage_data': self._serialize_coverage_data(coverage_data)
            }
            
            if result.overall_success:
                logger.info("✓ Coverage data collected successfully")
            else:
                logger.info("✗ No coverage data collected")
            
        except Exception as e:
            logger.error(f"Coverage evaluation failed with exception: {e}")
            result.overall_success = False
            result.model_checking_error = str(e)
            
        return result
    
    def _generate_basic_config_file(self, spec_file_path: str, output_dir: Path, task_name: str, model_name: str) -> str:
        """
        Generate a basic TLC configuration file for a TLA+ specification using ConfigGenerator.
        
        Args:
            spec_file_path: Path to the TLA+ specification file
            output_dir: Output directory for the config file
            task_name: Task name for loading appropriate prompt
            model_name: Model name for config generation
            
        Returns:
            Path to the generated config file
        """
        # Read the specification content
        with open(spec_file_path, 'r', encoding='utf-8') as f:
            tla_content = f.read()
        
        # Use ConfigGenerator with empty invariants (same as runtime_check does)
        config_generator = ConfigGenerator()
        success, config_content, error = config_generator.generate_config(
            tla_content=tla_content,
            invariants="",  # Empty invariants for basic config
            task_name=task_name,
            model_name=model_name
        )
        
        if not success:
            raise Exception(f"Config generation failed: {error}")
        
        # Save config file
        spec_name = Path(spec_file_path).stem
        config_file_path = output_dir / f"{spec_name}.cfg"
        
        with open(config_file_path, 'w', encoding='utf-8') as f:
            f.write(config_content)
        
        logger.info(f"✓ Generated config file using ConfigGenerator: {config_file_path}")
        
        return str(config_file_path)
    
    def _run_tlc_with_coverage(self, spec_file_path: str, config_file_path: str, output_dir: Path) -> CoverageData:
        """
        Run TLC with coverage enabled and parse the output.
        
        Args:
            spec_file_path: Path to the TLA+ specification file
            config_file_path: Path to the TLC configuration file
            output_dir: Directory for logs and temporary files
            
        Returns:
            CoverageData: Parsed coverage data
        """
        # Prepare TLC command with coverage and tool mode
        cmd = [
            "java",
            "-cp", str(self.tlc_runner.tla_tools_path),  # Reuse TLC runner's path
            "tlc2.TLC",
            "-tool",  # Enable tool mode for structured output
            "-coverage", str(self.coverage_interval),  # Enable coverage statistics
            "-deadlock",  # Disable deadlock checking to avoid early termination
            "-config", Path(config_file_path).name,
            Path(spec_file_path).name
        ]
        
        logger.info(f"Running TLC with coverage: {' '.join(cmd)}")
        
        try:
            # Run TLC (similar to TLCRunner.run_model_checking)
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.tlc_timeout,
                cwd=Path(spec_file_path).parent  # Run in spec directory
            )
            
            # Parse coverage data from output
            combined_output = result.stdout + result.stderr
            coverage_data = self.parser.parse_tool_output(combined_output)
            
            # Save TLC output for debugging
            with open(output_dir / "tlc_coverage_output.log", 'w') as f:
                f.write(f"Command: {' '.join(cmd)}\n")
                f.write(f"Exit code: {result.returncode}\n")
                f.write(f"Working directory: {Path(spec_file_path).parent}\n")
                f.write(f"STDOUT:\n{result.stdout}\n")
                f.write(f"STDERR:\n{result.stderr}\n")
            
            logger.info(f"TLC coverage run completed (exit code: {result.returncode})")
            
            return coverage_data
            
        except subprocess.TimeoutExpired as e:
            logger.warning(f"TLC timed out after {self.tlc_timeout}s")
            # IMPORTANT: Parse coverage data from timeout output too!
            if hasattr(e, 'stdout') and hasattr(e, 'stderr'):
                # Handle both str and bytes output
                stdout_str = e.stdout.decode('utf-8') if isinstance(e.stdout, bytes) else (e.stdout or "")
                stderr_str = e.stderr.decode('utf-8') if isinstance(e.stderr, bytes) else (e.stderr or "")
                combined_output = stdout_str + stderr_str
                coverage_data = self.parser.parse_tool_output(combined_output)
                
                # Save timeout output for debugging
                with open(output_dir / "tlc_coverage_output.log", 'w') as f:
                    f.write(f"Command: {' '.join(cmd)}\n")
                    f.write(f"Status: TIMEOUT after {self.tlc_timeout}s\n")
                    f.write(f"Working directory: {Path(spec_file_path).parent}\n")
                    f.write(f"STDOUT:\n{stdout_str}\n")
                    f.write(f"STDERR:\n{stderr_str}\n")
                
                logger.info(f"Parsed coverage data from timeout output: {coverage_data.total_expressions} expressions, {coverage_data.total_variables} variables")
                return coverage_data
            else:
                logger.warning("No output available from timeout exception")
                return CoverageData()  # Return empty coverage data only if no output
        except Exception as e:
            logger.error(f"TLC coverage execution failed: {e}")
            return CoverageData()  # Return empty coverage data
    
    
    def _serialize_coverage_data(self, coverage_data: CoverageData) -> Dict[str, Any]:
        """
        Serialize coverage data for JSON storage.
        
        Args:
            coverage_data: Coverage data to serialize
            
        Returns:
            Serializable dictionary
        """
        return {
            'variable_coverage': coverage_data.variable_coverage,
            'action_coverage': {k: {'evaluations': v[0], 'new_states': v[1]} 
                               for k, v in coverage_data.action_coverage.items()},
            'init_coverage': {k: {'evaluations': v[0], 'new_states': v[1]} 
                             for k, v in coverage_data.init_coverage.items()},
            'expression_coverage': coverage_data.expression_coverage,
            'cost_coverage': {k: {'evaluations': v[0], 'cost': v[1]} 
                             for k, v in coverage_data.cost_coverage.items()},
            'summary': {
                'total_variables': coverage_data.total_variables,
                'total_actions': coverage_data.total_actions,
                'successful_actions': coverage_data.successful_actions,
                'total_expressions': coverage_data.total_expressions,
                'covered_expressions': coverage_data.covered_expressions,
                'total_evaluations': coverage_data.total_evaluations,
                'total_cost': coverage_data.total_cost
            }
        }
    
    def _get_evaluation_type(self) -> str:
        """Return the evaluation type identifier"""
        return "coverage"


def create_coverage_evaluator(tlc_timeout: int = 60, 
                             coverage_interval: int = 1) -> CoverageEvaluator:
    """
    Factory function to create a coverage evaluator.
    
    Args:
        tlc_timeout: Timeout for TLC model checking in seconds
        coverage_interval: Interval for coverage statistics in minutes
        
    Returns:
        CoverageEvaluator instance
    """
    return CoverageEvaluator(
        tlc_timeout=tlc_timeout,
        coverage_interval=coverage_interval
    )