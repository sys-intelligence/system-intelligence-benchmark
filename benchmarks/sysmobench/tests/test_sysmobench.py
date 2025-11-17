"""Test SysMoBench core functionality."""

import sys
import os
from pathlib import Path

# Setup paths
SYSMOBENCH_CORE = Path(__file__).parent.parent / "sysmobench_core"
sys.path.insert(0, str(SYSMOBENCH_CORE))

from tla_eval.tasks.loader import TaskLoader
from tla_eval.methods.base import GenerationOutput
from tla_eval.evaluation.syntax.compilation_check import CompilationCheckEvaluator


def test_task_loader_initialization():
    """Test that TaskLoader can be initialized."""
    original_cwd = os.getcwd()
    try:
        os.chdir(SYSMOBENCH_CORE)

        loader = TaskLoader(
            tasks_dir="tla_eval/tasks",
            cache_dir="data/repositories"
        )

        assert loader is not None, "Failed to create TaskLoader"
    finally:
        os.chdir(original_cwd)


def test_list_available_tasks():
    """Test that TaskLoader can list available tasks."""
    original_cwd = os.getcwd()
    try:
        os.chdir(SYSMOBENCH_CORE)

        loader = TaskLoader(
            tasks_dir="tla_eval/tasks",
            cache_dir="data/repositories"
        )

        tasks = loader.list_available_tasks()
        assert len(tasks) > 0, "No tasks found"
        assert 'spin' in tasks, "spin task not found"
    finally:
        os.chdir(original_cwd)


def test_task_loading_with_traces():
    """Test loading a task with traces."""
    original_cwd = os.getcwd()
    try:
        os.chdir(SYSMOBENCH_CORE)

        loader = TaskLoader(
            tasks_dir="tla_eval/tasks",
            cache_dir="data/repositories"
        )

        # Load spin task
        task = loader.load_task(
            task_name='spin',
            traces_folder='data/sys_traces/spin'
        )

        assert task is not None, "Failed to load task"
        assert task.source_code is not None, "Task has no source code"
        assert len(task.source_code) > 0, "Source code is empty"
        assert task.traces is not None, "Task has no traces"
        assert len(task.traces) > 0, "Traces list is empty"
        assert task.task_name == 'spin', f"Expected task_name 'spin', got {task.task_name}"
    finally:
        os.chdir(original_cwd)


def test_generation_output_compatibility():
    """Test GenerationOutput has backward-compatible generated_text field."""
    test_spec = "---- MODULE Test ----\nNext == TRUE\n===="

    output = GenerationOutput(
        tla_specification=test_spec,
        method_name="test_method",
        task_name="test_task",
        metadata={},
        success=True
    )

    # Test both fields exist and are equal
    assert hasattr(output, 'tla_specification'), "Missing tla_specification field"
    assert hasattr(output, 'generated_text'), "Missing generated_text field"
    assert output.tla_specification == output.generated_text, "Fields are not equal"
    assert len(output.generated_text) > 0, "generated_text is empty"


def test_generation_output_fields():
    """Test GenerationOutput has all required fields."""
    output = GenerationOutput(
        tla_specification="test spec",
        method_name="test_method",
        task_name="test_task",
        metadata={"key": "value"},
        success=True,
        error_message=None
    )

    assert output.method_name == "test_method"
    assert output.task_name == "test_task"
    assert output.success is True
    assert output.error_message is None
    assert output.metadata["key"] == "value"


def test_compilation_evaluator_initialization():
    """Test CompilationCheckEvaluator can be instantiated."""
    original_cwd = os.getcwd()
    try:
        os.chdir(SYSMOBENCH_CORE)

        evaluator = CompilationCheckEvaluator(validation_timeout=60)
        assert evaluator is not None, "Failed to create CompilationCheckEvaluator"
    finally:
        os.chdir(original_cwd)


def test_compilation_evaluator_with_simple_spec():
    """Test CompilationCheckEvaluator with a simple TLA+ spec."""
    original_cwd = os.getcwd()
    try:
        os.chdir(SYSMOBENCH_CORE)

        evaluator = CompilationCheckEvaluator(validation_timeout=60)

        # Create a simple valid TLA+ spec (need to import standard modules)
        valid_spec = """---- MODULE SimpleTest ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
===="""

        output = GenerationOutput(
            tla_specification=valid_spec,
            method_name="test",
            task_name="test",
            metadata={},
            success=True
        )

        result = evaluator.evaluate(output, "test", "test", "test", "SimpleTest")

        # Should return a SyntaxEvaluationResult
        assert result is not None, "Evaluator returned None"
        assert hasattr(result, 'generation_successful'), "Result missing 'generation_successful' field"
        assert hasattr(result, 'task_name'), "Result missing 'task_name' field"
        assert result.task_name == "test", f"Expected task_name 'test', got {result.task_name}"
    finally:
        os.chdir(original_cwd)
