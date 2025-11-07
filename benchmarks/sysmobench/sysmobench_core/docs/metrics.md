# Metrics Design

## Overview

The quality evaluation of TLA+ specifications can be systematically divided into three fundamental dimensions:

1. **Syntax**: Compilability
2. **Semantics**: Logical coherence and executability (model checking)  
3. **System Consistency**: Consistency with actual system behavior

## 1. Syntax-Level Evaluation

### Current Challenges

The current syntax evaluation success rate is too low:
- **Direct compilation success rate**: ~20% for Claude Sonnet 4.0 generated specifications

### Proposed Improvements

#### 1.1 Action Decomposition Evaluation
Instead of evaluating the entire specification as a monolithic unit, decompose it into individual actions for separate assessment.

**Rationale**: Individual actions are smaller, more focused units that are easier to generate correctly. Also, **there are fewer errors caused by the interaction between actions.**

This approach yields ~90% success rate, providing better granularity for evaluation.

#### 1.2 Pass@k Evaluation
Adopt the pass@k metric from code generation benchmarks (HumanEval, MBPP) to account for the stochastic nature of LLM generation.

**Definition**: Given k generated solutions, pass@k measures the probability that at least one solution is syntactically correct.

## 2. Semantic-Level Evaluation

### Current Challenges

Semantic evaluation success rate is nearly 0.

### Proposed Improvements

#### 2.1 Pass@k for Semantic Correctness
Apply the pass@k approach.

#### 2.2 AST-based Static Analysis
Use static analysis to evaluate specification structure and complexity.

**Variable Count Analysis**: Check if the number of state variables matches system requirements. (Request in prompt)

**Branch Complexity Analysis**: Analyze control flow complexity through action definitions and conditional statements. While optimal complexity is hard to define, compare against reference implementations to detect under/over-modeling.

#### 2.3 LLM-based Quality Assessment
Use LLM evaluation to assess modeling quality by comparing source code and generated specification.

**Approach**: Provide both system source code and generated TLA+ specification to an LLM evaluator, asking it to score modeling accuracy, completeness, and abstraction quality.

**Rationale**: LLMs can understand both code semantics and formal specification patterns, potentially identifying subtle modeling issues that static analysis might miss.

## 3. System Consistency Evaluation

### Current Challenges

Trace validation presents the most significant challenges:
- **Trace validation success rate**: 0%
- **Alignment problem**: Manual intervention required to align instrumentation with specification actions.

### Proposed Improvements

#### 3.1 Comprehensive Instrumentation Strategy
Implement the most detailed possible instrumentation, then allow selective reduction based on specification requirements.

**Rationale**: Minimizes manual effort by providing comprehensive coverage upfront, then allowing targeted selection.

#### 3.2 Prompt-Guided Instrumentation Specification
Incorporate instrumentation granularity into the generation prompts to produce specifications that are directly compatible with trace validation.

#### 3.3 Progressive Granularity Trace Validation
Implement multi-level trace validation with increasing granularity to create smoother difficulty progression.

**Level 1 - Event-Only Traces**:

**Level 2 - Event + Basic State**: Add core state variables to traces (e.g., currentTerm, state role). 

**Level 3 - Event + Detailed State**: Include comprehensive state information.

**Rationale**: This progressive approach allows specifications to succeed at simpler levels while identifying their maximum validation capability, providing more nuanced evaluation than binary pass/fail.

