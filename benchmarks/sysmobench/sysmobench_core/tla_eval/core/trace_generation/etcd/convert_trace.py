#!/usr/bin/env python3
"""
ETCD Trace Converter CLI

Command-line interface for converting ETCD traces with support for:
- Default mapping from spec directory
- LLM-based mapping generation with --create-mapping
"""

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Optional

from trace_converter_impl import ETCDTraceConverterImpl


def main():
    parser = argparse.ArgumentParser(
        description='Convert ETCD system traces to TLA+ trace validation format'
    )

    # Required arguments
    parser.add_argument(
        'input_trace',
        type=str,
        help='Path to input trace file (NDJSON format)'
    )

    parser.add_argument(
        'output_trace',
        type=str,
        help='Path for output trace file'
    )

    # Optional arguments
    parser.add_argument(
        '--spec-path',
        type=str,
        help='Path to spec directory (used to find mapping file)',
        default=None
    )

    parser.add_argument(
        '--mapping-file',
        type=str,
        help='Path to custom mapping JSON file',
        default=None
    )

    # Mapping generation arguments
    parser.add_argument(
        '--create-mapping',
        action='store_true',
        help='Generate mapping file using LLM before conversion'
    )

    parser.add_argument(
        '--spec-file',
        type=str,
        help='TLA+ specification file (required with --create-mapping)'
    )

    parser.add_argument(
        '--model',
        type=str,
        help='LLM model to use for mapping generation (e.g., claude, gpt4)',
        default=None
    )

    parser.add_argument(
        '--mapping-output',
        type=str,
        help='Where to save generated mapping (defaults to spec directory)',
        default=None
    )

    args = parser.parse_args()

    # Validate arguments
    if args.create_mapping and not args.spec_file:
        parser.error("--spec-file is required when using --create-mapping")

    # Generate mapping if requested
    if args.create_mapping:
        print(f"Generating mapping from spec: {args.spec_file}")

        # Determine output path for mapping
        if args.mapping_output:
            mapping_output = args.mapping_output
        elif args.spec_path:
            mapping_output = os.path.join(args.spec_path, "etcd_mapping.json")
        elif args.spec_file:
            spec_dir = os.path.dirname(args.spec_file)
            mapping_output = os.path.join(spec_dir, "etcd_mapping.json")
        else:
            mapping_output = "etcd_mapping.json"

        # Generate the mapping
        result = ETCDTraceConverterImpl.generate_mapping_with_llm(
            spec_file=args.spec_file,
            model_name=args.model,
            output_path=mapping_output
        )

        if not result['success']:
            print(f"Error generating mapping: {result['error']}")
            sys.exit(1)

        print(f"Successfully generated mapping: {result['mapping_file']}")

        # Use the generated mapping for conversion
        if not args.mapping_file:
            args.mapping_file = result['mapping_file']

    # Determine spec path for default mapping lookup
    effective_spec_path = args.spec_path
    if not effective_spec_path and args.spec_file:
        effective_spec_path = os.path.dirname(args.spec_file)

    # Initialize converter
    converter = ETCDTraceConverterImpl(
        mapping_file=args.mapping_file,
        spec_path=effective_spec_path
    )

    # Perform conversion
    print(f"Converting trace: {args.input_trace} -> {args.output_trace}")
    print(f"Using mapping: {converter.mapping_file}")

    result = converter.convert_trace(
        input_trace_path=args.input_trace,
        output_trace_path=args.output_trace
    )

    if result['success']:
        print(f"Conversion successful!")
        print(f"  Input events: {result['input_events']}")
        print(f"  Output transitions: {result['output_transitions']}")
        print(f"  Output file: {result['output_file']}")
    else:
        print(f"Conversion failed: {result['error']}")
        sys.exit(1)


if __name__ == '__main__':
    main()