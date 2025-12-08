#!/usr/bin/env python3
"""
Example usage of ZooKeeper trace generation.

This script demonstrates various ways to use the ZooKeeper trace generator.
"""

from pathlib import Path
import sys

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent.parent))

from tla_eval.core.trace_generation.zookeeper.module import ZooKeeperTraceGenerator


def example_basic_generation():
    """Basic trace generation example."""
    print("=" * 60)
    print("Example 1: Basic Trace Generation")
    print("=" * 60)

    generator = ZooKeeperTraceGenerator()

    # Simple configuration
    config = {
        'num_traces': 3,
        'simulation_depth': 50,
        'max_crashes': 1
    }

    output_dir = Path("output/zookeeper/basic")
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"\nGenerating {config['num_traces']} traces...")
    results = generator.generate_traces(
        config=config,
        output_dir=output_dir,
        name_prefix="zk_basic"
    )

    print(f"\nResults:")
    for i, result in enumerate(results, 1):
        if result['success']:
            print(f"  [{i}] ✓ {result['trace_file']}")
            print(f"      Events: {result['event_count']}, "
                  f"Time: {result['replay_time']:.2f}s")
        else:
            print(f"  [{i}] ✗ Failed: {result['error']}")


def example_scenario_based():
    """Generate traces using predefined scenarios."""
    print("\n" + "=" * 60)
    print("Example 2: Scenario-Based Generation")
    print("=" * 60)

    generator = ZooKeeperTraceGenerator()
    scenarios = generator.get_available_scenarios()

    print("\nAvailable scenarios:")
    for name, config in scenarios.items():
        print(f"  - {name}: {config.get('description', 'No description')}")

    # Use "with_failures" scenario
    config = scenarios['with_failures'].copy()
    config['num_traces'] = 5

    output_dir = Path("output/zookeeper/scenarios")
    output_dir.mkdir(parents=True, exist_ok=True)

    print(f"\nGenerating {config['num_traces']} traces with 'with_failures' scenario...")
    results = generator.generate_traces(
        config=config,
        output_dir=output_dir,
        name_prefix="zk_failure"
    )

    success_count = sum(1 for r in results if r['success'])
    print(f"\nGenerated {success_count}/{config['num_traces']} traces successfully")


def example_batch_generation():
    """Generate multiple batches with different configurations."""
    print("\n" + "=" * 60)
    print("Example 3: Batch Generation with Multiple Configs")
    print("=" * 60)

    generator = ZooKeeperTraceGenerator()

    # Different configurations to try
    configs = [
        {
            'name': 'short_traces',
            'num_traces': 5,
            'simulation_depth': 30,
            'max_crashes': 0
        },
        {
            'name': 'with_crashes',
            'num_traces': 5,
            'simulation_depth': 80,
            'max_crashes': 2
        },
        {
            'name': 'with_partitions',
            'num_traces': 3,
            'simulation_depth': 100,
            'max_crashes': 1,
            'max_partitions': 1
        }
    ]

    all_results = {}

    for cfg in configs:
        name = cfg.pop('name')
        output_dir = Path(f"output/zookeeper/batch/{name}")
        output_dir.mkdir(parents=True, exist_ok=True)

        print(f"\n--- Generating '{name}' batch ---")
        results = generator.generate_traces(
            config=cfg,
            output_dir=output_dir,
            name_prefix=name
        )

        all_results[name] = results
        success = sum(1 for r in results if r['success'])
        print(f"    Result: {success}/{cfg['num_traces']} successful")

    # Summary
    print("\n" + "-" * 60)
    print("Batch Generation Summary:")
    print("-" * 60)
    for name, results in all_results.items():
        total = len(results)
        success = sum(1 for r in results if r['success'])
        avg_events = sum(r.get('event_count', 0) for r in results if r['success']) / max(success, 1)
        print(f"  {name:20s}: {success}/{total} traces, avg {avg_events:.0f} events")


def example_error_handling():
    """Demonstrate error handling and retry logic."""
    print("\n" + "=" * 60)
    print("Example 4: Error Handling with Retry")
    print("=" * 60)

    generator = ZooKeeperTraceGenerator()

    # Configuration with retry logic
    config = {
        'num_traces': 5,
        'generation_factor': 2.0,  # Generate 2x for redundancy
        'max_attempts': 3,         # Try up to 3 times
        'simulation_depth': 100,
        'max_crashes': 2
    }

    output_dir = Path("output/zookeeper/retry")
    output_dir.mkdir(parents=True, exist_ok=True)

    print("\nConfiguration:")
    print(f"  Target: {config['num_traces']} traces")
    print(f"  Redundancy factor: {config['generation_factor']}")
    print(f"  Max attempts: {config['max_attempts']}")

    results = generator.generate_traces(
        config=config,
        output_dir=output_dir,
        name_prefix="zk_retry"
    )

    # Analyze results
    successful = [r for r in results if r['success']]
    failed = [r for r in results if not r['success']]

    print(f"\nResults:")
    print(f"  Successful: {len(successful)}/{config['num_traces']}")
    print(f"  Failed: {len(failed)}")

    if failed:
        print("\nFailure reasons:")
        for i, result in enumerate(failed, 1):
            print(f"  [{i}] {result.get('error', 'Unknown error')}")


def example_trace_analysis():
    """Analyze generated traces."""
    print("\n" + "=" * 60)
    print("Example 5: Trace Analysis")
    print("=" * 60)

    generator = ZooKeeperTraceGenerator()

    config = {'num_traces': 3, 'simulation_depth': 80}
    output_dir = Path("output/zookeeper/analysis")
    output_dir.mkdir(parents=True, exist_ok=True)

    print("\nGenerating traces for analysis...")
    results = generator.generate_traces(
        config=config,
        output_dir=output_dir,
        name_prefix="zk_analyze"
    )

    successful = [r for r in results if r['success']]

    if not successful:
        print("No successful traces to analyze")
        return

    print(f"\nAnalyzing {len(successful)} traces...")

    # Collect statistics
    event_counts = [r['event_count'] for r in successful]
    replay_times = [r['replay_time'] for r in successful]

    print("\nStatistics:")
    print(f"  Event counts: min={min(event_counts)}, "
          f"max={max(event_counts)}, "
          f"avg={sum(event_counts)/len(event_counts):.1f}")
    print(f"  Replay times: min={min(replay_times):.2f}s, "
          f"max={max(replay_times):.2f}s, "
          f"avg={sum(replay_times)/len(replay_times):.2f}s")

    # Show trace contents
    print("\nSample events from first trace:")
    if successful:
        trace_file = Path(successful[0]['trace_file'])
        if trace_file.exists():
            with open(trace_file) as f:
                for i, line in enumerate(f):
                    if i >= 5:  # Show first 5 events
                        break
                    import json
                    event = json.loads(line)
                    print(f"  [{i}] {event.get('event', 'N/A'):30s} "
                          f"node={event.get('node', 'N/A')}")


def main():
    """Run all examples."""
    examples = [
        ("Basic Generation", example_basic_generation),
        ("Scenario-Based", example_scenario_based),
        ("Batch Generation", example_batch_generation),
        ("Error Handling", example_error_handling),
        ("Trace Analysis", example_trace_analysis),
    ]

    print("ZooKeeper Trace Generation Examples")
    print("=" * 60)
    print("\nAvailable examples:")
    for i, (name, _) in enumerate(examples, 1):
        print(f"  {i}. {name}")

    print("\nRunning all examples...")
    print("(This may take several minutes)")

    for name, func in examples:
        try:
            func()
        except KeyboardInterrupt:
            print("\n\nInterrupted by user")
            break
        except Exception as e:
            print(f"\nError in {name}: {e}")
            import traceback
            traceback.print_exc()

    print("\n" + "=" * 60)
    print("Examples complete!")
    print("=" * 60)


if __name__ == "__main__":
    main()
