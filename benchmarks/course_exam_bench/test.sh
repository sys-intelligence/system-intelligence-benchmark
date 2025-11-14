#!/bin/bash

set -e  # Exit immediately on error.

source .venv/bin/activate
pytest --version
pytest tests/ -v
deactivate

echo "==> CourseExamBench tests completed successfully."
