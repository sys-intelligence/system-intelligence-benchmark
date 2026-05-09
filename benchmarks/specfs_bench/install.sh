#!/bin/bash

set -e

if [ -d ".venv" ]; then
	echo "==> .venv already exists, skipping creation."
else
	echo "==> Creating .venv ..."
	python3 -m venv .venv
fi

source .venv/bin/activate
pip install --upgrade pip
pip install -r requirements.txt
deactivate

echo "✅ SpecFS benchmark environment is set up successfully."
echo "👉 To activate the virtual environment, run: source .venv/bin/activate"
