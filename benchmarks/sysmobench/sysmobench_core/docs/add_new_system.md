# Adding a New System to the Framework

This document explains how to add a new system to the framework. The process consists of three main steps:

## 1. Define Task Configuration

Create task definition in `tla_eval/tasks/<system_name>` directory:

### task.yaml
Create a system configuration file containing:
- Basic system information (name, etc.)
- Repository information (URL, branch, version)
- Source file paths
- TLA+ specification module name

### prompts directory
Create prompt files based on etcd naming convention:
- `agent_based.txt` - Agent-based generation prompt
- `direct_call.txt` - Direct call prompt
- `phase2_config.txt` - .cfg configuration file generation prompt
- `phase3_invariant_implementation.txt` - invariant translation prompt
- `trace_config_generation.txt` - Trace configuration generation prompt

## 2. Create Invariant Templates

Create invariant definitions in `data/invariant_templates/<system_name>` directory:

### invariants.yaml
Define core system invariants, each containing:
- `name` - Invariant name
- `type` - Safety or liveness
- `natural_language` - Natural language description
- `formal_description` - Formal description
- `tla_example` - TLA+ code example

These templates are used for invariant verification.

## 3. Implement Trace Validation

Implement `module.py` in `tla_eval/core/trace_generation/<system_name>` directory:

### Required Interface Classes
- `TraceGenerator` - Implements trace generation logic
- `TraceConverter` - Implements trace format conversion
- `SystemModule` - System module entry point

