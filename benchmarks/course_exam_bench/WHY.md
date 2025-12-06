# Why System Exam Benchmark?

The System Exam Benchmark evaluates whether AI agents possess foundational knowledge of core system concepts—the theoretical underpinnings necessary to reason about distributed systems, operating systems, concurrency, and fault tolerance. By testing models on real university course exams, we measure their ability to understand fundamental principles before attempting practical implementation tasks.

## Goals and Objectives

System intelligence requires more than pattern matching or code completion; it demands a deep understanding of how computing systems operate, fail, and scale. The System Exam Benchmark targets this foundational layer by presenting questions that require:

1. **Conceptual Reasoning**: Understanding distributed consensus protocols (e.g., Raft, Paxos), consistency models, and synchronization primitives
2. **Analytical Thinking**: Diagnosing failure scenarios, reasoning about race conditions, and evaluating trade-offs in system design
3. **Theoretical Knowledge**: Grasping correctness properties, performance characteristics, and fundamental limitations of system architectures

By using actual MIT course exams (6.5840 Distributed Systems, 6.1810 Operating Systems), we ensure questions reflect real educational standards and cover topics systems engineers must master. The benchmark includes single-choice, multiple-choice, true/false, and short-answer questions, allowing us to evaluate both factual recall and deeper analytical capabilities.

## How This Fits Into System Intelligence

The exam benchmark serves as a **prerequisite check** within the broader system intelligence vision. An AI agent that cannot explain why two-phase commit differs from Raft, or identify race conditions in concurrent code, will struggle with more complex tasks like debugging distributed systems, evaluating research artifacts, or designing fault-tolerant architectures.

This benchmark complements practical benchmarks (e.g., System Lab, ArtEvalBench) by:

- **Establishing Baseline Knowledge**: Verifying the model understands core concepts before applying them
- **Measuring Depth vs. Breadth**: Short-answer questions reveal whether models truly comprehend underlying mechanisms or merely memorize surface patterns
- **Providing Calibrated Comparison**: Real student performance data lets us contextualize AI capabilities against human learners

Ultimately, passing system exams demonstrates that an AI agent has internalized the conceptual foundation needed to tackle real-world system challenges—making it a critical stepping stone toward full system intelligence.
