#!/bin/bash

# Batch trace generation script for RedisRaft
# Generates 100 traces with depth ~100 events each

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUTPUT_BASE="/home/ubuntu/LLM_Gen_TLA_benchmark_framework/data/sys_traces/redisraft"
GENERATOR="$SCRIPT_DIR/raft_trace_generator"

# Configuration
NUM_TRACES=100
NODES=3
DURATION=20  # 20 seconds should generate ~100 events efficiently

echo "========================================"
echo "RedisRaft Batch Trace Generation"
echo "========================================"
echo "Number of traces: $NUM_TRACES"
echo "Nodes per cluster: $NODES"
echo "Duration per trace: ${DURATION}s"
echo "Output directory: $OUTPUT_BASE"
echo "========================================"

# Create output directory
mkdir -p "$OUTPUT_BASE"

# Build the generator
echo "Building trace generator..."
cd "$SCRIPT_DIR"
make clean && make

# Generate traces
for i in $(seq 1 $NUM_TRACES); do
    echo "Generating trace $i/$NUM_TRACES..."

    # Create unique output directory for this trace
    TRACE_DIR="$OUTPUT_BASE/trace_$(printf "%03d" $i)"
    mkdir -p "$TRACE_DIR"

    # Run generator with specified parameters
    if timeout $((DURATION + 10))s "$GENERATOR" $NODES $DURATION "$TRACE_DIR" > /dev/null 2>&1; then
        # Count events in generated traces
        TOTAL_EVENTS=0
        for node_file in "$TRACE_DIR"/*.ndjson; do
            if [ -f "$node_file" ]; then
                EVENTS=$(wc -l < "$node_file")
                TOTAL_EVENTS=$((TOTAL_EVENTS + EVENTS))
            fi
        done
        echo "  ✓ Trace $i complete: $TOTAL_EVENTS total events"
    else
        echo "  ✗ Trace $i failed or timed out"
        rm -rf "$TRACE_DIR"
    fi

    # Small delay to ensure clean separation
    sleep 1
done

echo "========================================"
echo "Batch generation complete!"
echo "Generated traces in: $OUTPUT_BASE"

# Summary statistics
SUCCESSFUL_TRACES=$(find "$OUTPUT_BASE" -name "trace_*" -type d | wc -l)
echo "Successful traces: $SUCCESSFUL_TRACES/$NUM_TRACES"

if [ $SUCCESSFUL_TRACES -gt 0 ]; then
    echo "Calculating average trace depth..."
    TOTAL_ALL_EVENTS=0
    for trace_dir in "$OUTPUT_BASE"/trace_*; do
        if [ -d "$trace_dir" ]; then
            TRACE_EVENTS=0
            for node_file in "$trace_dir"/*.ndjson; do
                if [ -f "$node_file" ]; then
                    EVENTS=$(wc -l < "$node_file")
                    TRACE_EVENTS=$((TRACE_EVENTS + EVENTS))
                fi
            done
            TOTAL_ALL_EVENTS=$((TOTAL_ALL_EVENTS + TRACE_EVENTS))
        fi
    done
    AVG_DEPTH=$((TOTAL_ALL_EVENTS / SUCCESSFUL_TRACES))
    echo "Average trace depth: $AVG_DEPTH events"
fi

echo "========================================"