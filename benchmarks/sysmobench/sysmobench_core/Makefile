# TLA+ Evaluation Framework Makefile

.PHONY: install install-dev test lint format clean build help

# Default target
help:
	@echo "Available commands:"
	@echo "  install      Install the package"
	@echo "  install-dev  Install with development dependencies"
	@echo "  test         Run tests"
	@echo "  lint         Run linting checks"
	@echo "  format       Format code with black"
	@echo "  clean        Clean build artifacts"
	@echo "  build        Build the package"
	@echo "  example      Run example benchmark"

# Installation
install:
	pip install -e .

install-dev:
	pip install -e ".[dev]"

# Testing
test:
	pytest tests/ -v

# Code quality
lint:
	flake8 tla_eval/ tests/
	mypy tla_eval/

format:
	black tla_eval/ tests/ scripts/

# Build and cleanup
build:
	python -m build

clean:
	rm -rf build/
	rm -rf dist/
	rm -rf *.egg-info/
	find . -type d -name __pycache__ -delete
	find . -type f -name "*.pyc" -delete

# Example usage
example:
	python3 scripts/run_benchmark.py --method direct_call --task etcd --dry-run

# Test models
test-models:
	python3 scripts/test_models.py