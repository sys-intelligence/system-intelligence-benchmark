#!/bin/bash

set -e  # Exit immediately on error.

source .venv/bin/activate
pytest --version
pytest
deactivate

echo "==> ExampleBench test is done successfully."
