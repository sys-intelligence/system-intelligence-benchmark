# Why System Lab Benchmark?

The System Lab Benchmark evaluates AI agents on their ability to complete realistic, hands-on system programming assignments from university courses. Unlike exam questions that test conceptual understanding, labs require end-to-end implementation: reading complex codebases, designing concurrent algorithms, writing race-free code, and passing comprehensive test suites. This benchmark measures whether agents can translate theoretical knowledge into working system components.

## Goals and Objectives

Building real systems demands capabilities far beyond answering conceptual questions. The System Lab Benchmark targets practical system intelligence by requiring agents to:

1. **Navigate Complex Codebases**: Understand existing Go implementations of distributed systems (MapReduce, Raft, key-value stores) spanning thousands of lines
2. **Implement Distributed Algorithms**: Write correct implementations of consensus protocols, replication strategies, and fault-tolerant services
3. **Handle Concurrency**: Reason about race conditions, design thread-safe data structures, and use synchronization primitives correctly
4. **Pass Rigorous Tests**: Satisfy comprehensive test suites covering normal operation, concurrent execution, and crash recovery scenarios

By using actual MIT 6.5840 Distributed Systems labs, we ensure tasks reflect real-world complexity students encounter when learning to build production-grade systems. Success requires not just generating syntactically correct code, but producing implementations that are correct, efficient, and robust under adversarial conditions.

## How This Fits Into System Intelligence

The lab benchmark represents the **bridge from theory to practice** in system intelligence. While the System Exam Benchmark tests whether agents understand distributed consensus conceptually, the System Lab Benchmark tests whether they can actually implement Raft correctly—a significantly harder challenge requiring:

- **Code Comprehension**: Reading and understanding starter code, existing interfaces, and test harnesses
- **Algorithmic Precision**: Translating protocol specifications into correct, debuggable implementations
- **Systems Thinking**: Managing state machines, handling asynchronous events, and reasoning about partial failures
- **Iterative Debugging**: Diagnosing test failures, fixing race conditions, and ensuring correctness under stress

This benchmark complements other system intelligence tasks:

- **Versus System Exam**: Moves from "can you explain Raft?" to "can you build Raft?"
- **Versus ArtEvalBench**: Focuses on creating new implementations rather than evaluating existing artifacts
- **Versus SysMoBench**: Emphasizes executable code in Go rather than formal TLA+ specifications

Completing system labs demonstrates an agent can work as a practical systems engineer—turning designs into reliable, tested implementations that handle real-world complexity. This makes it essential for achieving full system intelligence.
