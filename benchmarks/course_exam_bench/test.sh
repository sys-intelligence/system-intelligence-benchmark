#!/bin/bash

set -e  # Exit immediately on error.

source envexamplebench/bin/activate
pytest --version
pytest
deactivate

echo "==> ExampleBench test is done successfully."
