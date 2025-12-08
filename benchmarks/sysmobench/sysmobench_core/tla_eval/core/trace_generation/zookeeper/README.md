# ZooKeeper Trace Generation

ZooKeeper system-level trace generation using the Remix framework.

## Overview

This module generates real system traces for ZooKeeper by leveraging the Remix infrastructure:

1. **TLC Model Checker**: Generates model-level traces from TLA+ specification
2. **AspectJ Instrumentation**: Intercepts ZooKeeper execution during replay
3. **NDJSON Output**: Collects system-level events in standardized format

## Architecture

```
Python API (module.py)
    ↓
ZooKeeperCluster (cluster.py)
    ↓
    ├─→ TLC Model Checker (generates model traces)
    ├─→ Trace Parser (converts to JSON)
    ├─→ Replay Service (runs instrumented ZooKeeper)
    └─→ NDJSON Collector (captures system events)
```

## Prerequisites

### Required Software

- **Java 11+**: For running Remix/ZooKeeper
- **Maven 3.5+**: For building Remix checker
- **Python 3.8+**: For trace generation API

### Remix Setup

The Remix framework must be available at:
```
data/repositories/Remix/
```

To build Remix checker:
```bash
cd data/repositories/Remix/scripts
./build.sh
```

## Usage

### Basic Usage

```python
from tla_eval.core.trace_generation.registry import get_system

# Get ZooKeeper system
zk_system = get_system("zookeeper")
generator = zk_system.get_trace_generator()

# Generate 5 traces
config = {
    'num_traces': 5,
    'simulation_depth': 100,
    'max_crashes': 2
}

results = generator.generate_traces(
    config=config,
    output_dir=Path("data/traces/zookeeper"),
    name_prefix="zk_trace"
)

# Check results
for result in results:
    if result['success']:
        print(f"✓ Generated: {result['trace_file']}")
        print(f"  Events: {result['event_count']}")
        print(f"  Replay time: {result['replay_time']:.2f}s")
    else:
        print(f"✗ Failed: {result['error']}")
```

### Configuration Options

```python
config = {
    # Quantity control
    'num_traces': 10,           # Number of traces to generate
    'generation_factor': 1.5,   # Generate 1.5x for redundancy
    'max_attempts': 3,          # Max retry attempts

    # TLC parameters
    'simulation_depth': 100,    # Maximum trace length
    'max_crashes': 2,           # Max node crashes
    'max_epoch': 3,             # Max ZAB epochs
    'max_transactions': 2,      # Max transactions
    'max_partitions': 0,        # Max network partitions
    'max_timeout_failures': 6   # Max timeout failures
}
```

### Predefined Scenarios

```python
# Get available scenarios
scenarios = generator.get_available_scenarios()

# Use a specific scenario
config = scenarios['with_failures']
config['num_traces'] = 10

results = generator.generate_traces(config, output_dir, "failure_trace")
```

Available scenarios:
- **normal_operation**: No failures, basic operation
- **with_failures**: Node crashes and network partitions
- **leader_election**: Focus on leader election
- **stress_test**: High complexity with many failures

## Output Format

### NDJSON Trace Format

Each line is a JSON object representing an event:

```json
{"event": "ElectionMessage", "step": 0, "node": "s0", "subnode": 1, "data": {...}}
{"event": "LocalEvent", "step": 1, "node": "s1", "subnode": 2, "data": {...}}
{"event": "LeaderToFollowerMessage", "step": 2, "node": "s0", "subnode": 3, "data": {...}}
```

Fields:
- `event`: Event type (e.g., ElectionMessage, LocalEvent)
- `step`: Sequential step number
- `node`: Node identifier (e.g., "s0", "s1")
- `subnode`: Subnode/thread identifier
- `data`: Event-specific data (type, payload, zxid, etc.)

### Event Types

- **ElectionMessage**: Leader election messages
- **LocalEvent**: Local state changes (logging, commit, etc.)
- **FollowerToLeaderMessage**: Follower→Leader communication
- **LeaderToFollowerMessage**: Leader→Follower communication

## Implementation Details

### Quantity Control

The generator ensures exact quantity through:

1. **Redundancy**: Generates `num_traces * generation_factor` model traces
2. **Filtering**: Keeps only successful replays
3. **Retry**: Multiple attempts if needed
4. **Early Stop**: Stops when target reached

### Workflow

```
1. Update Zab-simulate.ini with parameters
2. Run TLC to generate N model traces
3. Parse traces to JSON format
4. For each trace:
   a. Set NDJSON_OUTPUT environment variable
   b. Run Remix replay with instrumented ZooKeeper
   c. Collect NDJSON events from AspectJ hooks
   d. Verify output file created
5. Return successful traces (up to num_traces)
```

### Error Handling

- **TLC Failure**: Returns error, can retry
- **Parse Failure**: Skips to next attempt
- **Replay Timeout**: 5-minute timeout per trace
- **High Failure Rate**: Stops batch if >50% fail

## Trace Converter

Convert traces to TLA+ spec-compatible format:

```python
converter = zk_system.get_trace_converter()

result = converter.convert_trace(
    input_path=Path("raw_trace.ndjson"),
    output_path=Path("converted_trace.ndjson")
)

if result['success']:
    print(f"Converted {result['input_events']} events")
    print(f"Output: {result['output_file']}")
```

## Troubleshooting

### Issue: "Remix not found"

Ensure Remix is cloned and at correct location:
```bash
ls data/repositories/Remix/
```

### Issue: "TLC generation failed"

Check TLC output:
```bash
cd data/repositories/Remix/generator
cat output/model_random_*/MC.out
```

### Issue: "No NDJSON generated"

1. Verify Remix is built with patch:
   ```bash
   cd data/repositories/Remix/scripts
   ./build.sh
   ```

2. Check Java logs in `results/` directory

3. Verify environment variable is passed correctly

### Issue: "High failure rate"

Try adjusting parameters:
- Reduce `simulation_depth`
- Reduce `max_crashes`
- Increase `generation_factor`

## Performance

Typical generation times (on standard hardware):

- **TLC generation**: 10-30 seconds for 10 traces
- **Trace parsing**: 1-2 seconds
- **Replay per trace**: 10-60 seconds depending on depth
- **Total**: ~2-10 minutes for 10 traces

Optimization tips:
- Use `generation_factor` > 1 to reduce retry overhead
- Reduce `simulation_depth` for faster traces
- Run multiple batches in parallel (separate processes)

## Examples

See `examples/zookeeper_trace_generation.py` for complete examples:
- Basic generation
- Batch generation with different scenarios
- Error handling and retry logic
- Trace analysis
