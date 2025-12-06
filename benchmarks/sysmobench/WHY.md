# Why Formal System Modeling?

SysMoBench evaluates whether AI agents can translate complex, real-world concurrent and distributed systems into rigorous formal specifications using TLA+. Formal modeling is essential for verifying correctness properties of critical systems, but writing and maintaining such specifications is notoriously difficult and time-consuming. This benchmark tests whether agents can bridge the gap between implementation code and mathematical models—a key capability for building trustworthy systems.

## Goals and Objectives

Formal verification provides the strongest guarantees of system correctness, yet remains underutilized because writing formal specifications requires deep expertise. SysMoBench targets this challenge by evaluating AI agents on their ability to:

1. **Comprehend Complex Systems**: Analyze real-world source code (Rust, Go, C) implementing concurrent primitives, consensus protocols, and distributed services
2. **Abstract Critical Properties**: Identify essential behaviors while omitting implementation details irrelevant to correctness
3. **Generate Executable Specifications**: Produce syntactically correct TLA+ code that passes compilation (SANY), runs successfully (TLC), and satisfies invariants
4. **Validate Against Real Behavior**: Ensure generated specifications conform to actual system execution traces and maintain specified safety/liveness properties

The benchmark includes nine diverse systems spanning concurrency primitives (Asterinas spinlock/mutex/rwmutex), consensus protocols (Etcd Raft, Redis Raft, Xline CURP), and distributed services (PGo dqueue/locksvc/raftkvs). Success requires agents to handle systems ranging from 175 to 4,064 lines of source code and produce TLA+ specifications from 75 to 508 lines.

## How This Fits Into System Intelligence

Formal modeling represents the **highest level of system abstraction**—moving from executable code to mathematical reasoning about correctness. This capability is crucial for system intelligence because:

- **Verification at Scale**: As systems grow more complex, manual testing cannot provide exhaustive correctness guarantees; formal methods can
- **Design Before Implementation**: Modeling systems in TLA+ before writing code can catch design flaws early, when they're cheapest to fix
- **Understanding Existing Systems**: Reverse-engineering formal models from legacy code helps document assumptions, invariants, and subtle correctness properties

SysMoBench complements other system benchmarks by testing a unique combination of capabilities:

- **Versus System Exam**: Moves beyond conceptual understanding to producing executable formal specifications
- **Versus System Lab**: Requires abstraction and mathematical reasoning rather than concrete implementation
- **Versus ArtEvalBench**: Focuses on specification and verification rather than artifact reproduction
- **Versus Cache Algorithm Benchmark**: Emphasizes correctness properties over performance optimization

The benchmark's four-phase evaluation pipeline (syntax → runtime → trace conformance → invariant verification) ensures agents don't just generate plausible-looking TLA+ code, but produce specifications that:

1. **Compile Successfully**: Pass SANY type-checking and syntax validation
2. **Execute Correctly**: Run without errors or deadlocks in TLC model checker
3. **Match Real Behavior**: Conform to execution traces collected from actual system implementations
4. **Preserve Invariants**: Satisfy safety and liveness properties specific to each system

## System Intelligence Impact

Achieving competence on SysMoBench would mark a significant milestone for AI-assisted system development. An agent that can reliably translate system implementations into TLA+ specifications could:

- **Accelerate Verification**: Reduce months of manual modeling effort to hours or days
- **Democratize Formal Methods**: Make rigorous verification accessible to engineers without specialized training
- **Improve System Reliability**: Enable verification of critical systems (filesystems, databases, distributed protocols) that currently rely primarily on testing
- **Support Incremental Development**: As systems evolve, automatically update specifications to match implementation changes

By testing agents on real-world systems rather than toy examples, SysMoBench ensures progress toward practical formal verification assistance—a critical component of building trustworthy, verifiable computing systems at scale.
