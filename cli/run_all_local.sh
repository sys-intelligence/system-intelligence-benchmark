#!/bin/bash

# Script to run install.sh and run.sh for all benchmarks
# Usage: ./run_all_local.sh <model> [agent]

set -e  # Exit immediately on error.

MODEL="$1"
AGENT="${2:-}"

if [ -z "$MODEL" ]; then
    echo "Error: Model parameter is required"
    echo "Usage: $0 <model> [agent]"
    echo "Example: $0 gpt-4o"
    echo "Example: $0 gpt-4o agent_based"
    exit 1
fi

BENCHMARKS_DIR="../benchmarks"

# Check if benchmarks directory exists
if [ ! -d "$BENCHMARKS_DIR" ]; then
    echo "Error: $BENCHMARKS_DIR directory not found"
    exit 1
fi

if [ -n "$AGENT" ]; then
    echo "Running all benchmarks with model: $MODEL and agent: $AGENT"
else
    echo "Running all benchmarks with model: $MODEL"
fi
echo ""

# Iterate through each subdirectory in benchmarks
for bench_dir in "$BENCHMARKS_DIR"/*/; do
    if [ -d "$bench_dir" ]; then
        bench_name=$(basename "$bench_dir")
        echo "========================================"
        echo "Processing benchmark: $bench_name"
        echo "========================================"

        # Run install.sh if it exists
        if [ -f "$bench_dir/install.sh" ]; then
            echo "Running install.sh for $bench_name..."
            cd "$bench_dir" && bash install.sh
            cd - > /dev/null
        else
            echo "Warning: install.sh not found in $bench_dir"
        fi

        # Run run.sh if it exists
        if [ -f "$bench_dir/run.sh" ]; then
            if [ -n "$AGENT" ]; then
                echo "Running run.sh for $bench_name with model $MODEL and agent $AGENT..."
                cd "$bench_dir" && bash run.sh "$MODEL" "$AGENT"
            else
                echo "Running run.sh for $bench_name with model $MODEL..."
                cd "$bench_dir" && bash run.sh "$MODEL"
            fi
            cd - > /dev/null
        else
            echo "Warning: run.sh not found in $bench_dir"
        fi

        echo ""
    fi
done

echo "All benchmarks processed."

# copy the results to a single directory
RESULTS_DIR="./"
mkdir -p "$RESULTS_DIR"
for bench_dir in "$BENCHMARKS_DIR"/*/; do
    if [ -d "$bench_dir/outputs" ]; then
        cp -r "$bench_dir/outputs" "$RESULTS_DIR/$bench_name"
    fi
done
echo "All benchmark results copied to $RESULTS_DIR"