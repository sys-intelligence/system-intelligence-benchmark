# CS530 Fall 2016 Midterm

```json
{
  "exam_id": "cs530_fall_2016_midterm",
  "test_paper_name": "CS530 Fall 2016 Midterm",
  "course": "CS530",
  "institution": "University of Waterloo",
  "year": 2016,
  "score_total": 52,
  "num_questions": 21
}
```

---

## Question 1 [2 point(s)]

List the semaphores that you will use in your solution. For each semaphore, state what its initial value should be.

```json
{
  "problem_id": "1",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "semaphores"],
  "answer": "SemA: initial value 2; SemB: initial value 1",
  "llm_judge_instructions": "Award 1 point for correctly naming SemA with initial value 2. Award 1 point for correctly naming SemB with initial value 1. 0 points for each incorrect or missing semaphore."
}
```

---

## Question 2 [8 point(s)]

Show the semaphore P and V instructions that threads should perform before and after each call to funcA and funcB to enforce the synchronization requirements.

```json
{
  "problem_id": "2",
  "points": 8,
  "type": "Freeform",
  "tags": ["concurrency", "semaphores"],
  "answer": "Before funcA: P(SemA); funcA(); After funcA: V(SemA); Before funcB: P(SemB); P(SemA); funcB(); After funcB: V(SemA); V(SemB);",
  "llm_judge_instructions": "Award 2 points if the operations before funcA are exactly 'P(SemA)'. Award 2 points if the operations after funcA are exactly 'V(SemA)'. Award 2 points if the operations before funcB are exactly 'P(SemB); P(SemA)'. Award 2 points if the operations after funcB are exactly 'V(SemA); V(SemB)'. If an individual part is partially correct (e.g., correct semaphores but wrong order), award at most 1 point for that part."
}
```

---

## Question 3 [2 point(s)]

Suppose that each thread accesses the shared variable exactly one time, and that all k threads do so at exactly the same time, which we will refer to as time t = 0. At what time will the last of the threads finish releasing the spinlock?

```json
{
  "problem_id": "3",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "spinlocks"],
  "answer": "t = 10k",
  "llm_judge_instructions": "Award 2 points if the answer is 't = 10k' or an equivalent algebraic expression. Award 0 points otherwise."
}
```

---

## Question 4 [2 point(s)]

For the same scenario described in part (a), what is the total amount of time that the threads will spend spinning? In other words, what is the sum of the threads’ spinning times?

```json
{
  "problem_id": "4",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "spinlocks"],
  "answer": "total time = 5(k^2 - k)",
  "llm_judge_instructions": "Award 2 points for the exact expression '5(k^2 - k)' or an algebraically equivalent expression. Award 1 point for demonstrating correct proportional relationship (e.g., stating 'O(k^2)') without the exact coefficient. 0 points otherwise."
}
```

---

## Question 5 [2 point(s)]

For this part of the question, assume that there are k threads timesharing a single processor. The first thing that each thread does when it is able to run is to acquire the spinlock and access the shared variable. Each thread accesses the shared variable one time. Assume that the scheduling quantum is larger than 10 time units. What is the total amount of time that the threads will spin?

```json
{
  "problem_id": "5",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "spinlocks"],
  "answer": "None of the threads will spin (total spinning time is zero).",
  "llm_judge_instructions": "Award 2 points if the answer states that the total spinning time is zero (or equivalent). Award 0 points otherwise."
}
```

---

## Question 6 [2 point(s)]

Assuming that no errors occur, are the following values for numbers possible after all threads have finished executing? For each, answer 'Yes' or 'No', and give a brief (one sentence) explanation.
numbers[10] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0}

```json
{
  "problem_id": "6",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "race-conditions"],
  "answer": "Yes. For example, this could occur if every instance of myThreadB runs and exits before any thread running myThreadA executes the line value = value + 1.",
  "llm_judge_instructions": "Award 2 points for answering 'Yes' and providing a concise one-sentence justification that explains how all zeros could occur. Award 0 points for incorrect answer or missing/incorrect justification."
}
```

---

## Question 7 [2 point(s)]

Repeat part (6), but for the following values for numbers:
numbers[10] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 12}

```json
{
  "problem_id": "7",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "race-conditions"],
  "answer": "No. Value starts at 0, and is incremented at most 10 times, so it could never be 12, regardless of thread execution order.",
  "llm_judge_instructions": "Award 2 points for answering 'No' with a correct one-sentence justification that explains the maximum possible total increments (at most 10). Award 0 points otherwise."
}
```

---

## Question 8 [2 point(s)]

Repeat part (6), but for the following values for numbers:
numbers[10] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}

```json
{
  "problem_id": "8",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "race-conditions"],
  "answer": "Yes. For example, this could occur if each pair myThreadA/myThreadB executes completely before the next myThreadA executes.",
  "llm_judge_instructions": "Award 2 points for answering 'Yes' with a concise justification explaining a possible execution order that yields the sequence 1..10. Award 0 points otherwise."
}
```

---

## Question 9 [2 point(s)]

Repeat part (6), but for the following values for numbers:
numbers[10] = {9, 8, 7, 6, 5, 4, 3, 2, 1, 0}

```json
{
  "problem_id": "9",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "race-conditions"],
  "answer": "Yes. For example, this can occur if threads run in decreasing order, and each thread’s myThreadB executes before the corresponding myThreadA increments the shared value.",
  "llm_judge_instructions": "Award 2 points for answering 'Yes' with a concise justification describing a valid execution order that produces the listed sequence. Award 0 points otherwise."
}
```

---

## Question 10 [2 point(s)]

Draw the relevant page-table-based address translation outcomes for the given data. Provide the physical address results or 'exception' for the listed virtual addresses as specified.

a) a[i] and i entry row 1:
0x000100F0 0x100 0x000321F0

```json
{
  "problem_id": "10",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "exception",
  "llm_judge_instructions": "Award 2 points if the student correctly indicates 'exception' for this translation scenario. Award 0 points otherwise."
}
```

---

## Question 11 [2 point(s)]

b) a[i] and i entry row 2:
0x00012A00 0x120 0x00010A12

```json
{
  "problem_id": "11",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "exception",
  "llm_judge_instructions": "Award 2 points if the student correctly indicates 'exception' for this translation scenario. Award 0 points otherwise."
}
```

---

## Question 12 [2 point(s)]

c) a[i] and i entry row 3:
0x0001305D 0x2 exception

```json
{
  "problem_id": "12",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "exception",
  "llm_judge_instructions": "Award 2 points if the student correctly indicates 'exception' for this translation scenario. Award 0 points otherwise."
}
```

---

## Question 13 [2 point(s)]

d) a[i] and i entry row 4:
0x00040EF0 0x1100 0x00022000

```json
{
  "problem_id": "13",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "0x00022000",
  "llm_judge_instructions": "Award 2 points if the student provides the correct physical address '0x00022000'. Award 0 points otherwise."
}
```

---

## Question 14 [2 point(s)]

e) a[i] and i entry row 5:
0x00041F00 0x100 exception

```json
{
  "problem_id": "14",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "exception",
  "llm_judge_instructions": "Award 2 points if the student correctly indicates 'exception' for this translation scenario. Award 0 points otherwise."
}
```

---

## Question 15 [3 point(s)]

On the MIPS, the load linked (ll) and store conditional (sc) instructions are used to implement spinlocks. Suppose that two threads, T1 and T2, try to acquire an unlocked spinlock at the same time, and that their ll and sc instructions execute in the following order:
T1: ll ... timell ↓ sc ... sc
Which thread(s) will acquire the spinlock after this sequence? Answer one of the following: T1, T2, both, neither.

```json
{
  "problem_id": "15",
  "points": 3,
  "type": "Freeform",
  "tags": ["mips", "spinlocks"],
  "answer": "T2",
  "llm_judge_instructions": "Award 3 points if the answer is 'T2' and the student explains that T2's sc succeeds while T1's sc fails due to T2's intervening operations. Award 0 points otherwise."
}
```

---

## Question 16 [3 point(s)]

Suppose that the MIPS spinlock was mistakenly implemented using a regular load instruction (lw, instead of ll) and a regular store instruction (sw, instead of sc). Suppose that the instruction sequence is the same as in part (15):
T1: lw ... timelw ↓ sw ... sw
Which thread(s) will believe that they have acquired the spinlock after this sequence? Answer one of the following: T1, T2, both, neither.

```json
{
  "problem_id": "16",
  "points": 3,
  "type": "Freeform",
  "tags": ["mips", "spinlocks"],
  "answer": "Both threads will believe they have acquired the spinlock.",
  "llm_judge_instructions": "Award 3 points if the answer is 'Both' and the student briefly explains that without LL/SC atomicity both loads/stores can succeed and both threads may think they acquired the lock. Award 0 points otherwise."
}
```

---

## Question 17 [2 point(s)]

What is the difference between a thread yielding and a thread blocking?

```json
{
  "problem_id": "17",
  "points": 2,
  "type": "Freeform",
  "tags": ["os", "scheduling"],
  "answer": "A thread that yields goes from running to ready and can be immediately scheduled again; a thread that is blocked is not running or ready, and waits on a resource until it becomes available.",
  "llm_judge_instructions": "Award 1 point for stating that yielding moves a thread from running to ready (it remains eligible for scheduling). Award 1 point for stating that blocking makes the thread wait for a resource and removes it from the ready state. 0 points for each missing or incorrect part."
}
```

---

## Question 18 [2 point(s)]

When an exception or interrupt occurs, a trap frame must be created to preserve the application’s context. This trap frame is put on a separate kernel stack, instead of the application’s stack: why?

```json
{
  "problem_id": "18",
  "points": 2,
  "type": "Freeform",
  "tags": ["os", "trap"],
  "answer": "Possible answers: •The stack pointer is an application-owned register, and thus can’t be trusted to be pointing at a valid stack. •Using the application stack would expose kernel data to the application. •Using the application stack would require the application to budget virtual memory for (unknown) kernel usage.",
  "llm_judge_instructions": "Award 1 point for any explanation that the application stack cannot be trusted or that it may not be valid. Award 1 point for any explanation about protecting kernel data/avoiding relying on application-provided memory. Partial credit allowed (1 point) if only one of the two major reasons is given correctly."
}
```

---

## Question 19 [2 point(s)]

Both wait channels and condition variables can be used to make threads block. How does a wait channel differ from a condition variable? In particular, how does wchan_sleep differ from cv_wait?

```json
{
  "problem_id": "19",
  "points": 2,
  "type": "Freeform",
  "tags": ["os", "wait-channels", "cv"],
  "answer": "Condition variables are used with an associated lock and cv_wait releases the lock while blocking; wait channels simply block the thread without the automatic lock-release semantics.",
  "llm_judge_instructions": "Award 1 point for stating that condition variables are used with an associated lock and that cv_wait atomically releases that lock while sleeping. Award 1 point for stating that wait channels block without providing automatic lock-release semantics. 0 points for each missing or incorrect part."
}
```

---

## Question 20 [2 point(s)]

Process P calls the fork syscall and creates process C. Process P exits before process C exits. Assume that the kernel does not allow a process to call waitpid on any process except its children. Are any of the following statements definitely true at the time that P exits? Circle any that are true.
• Process P’s PID can be safely re-used by the kernel.
• Process C inherits process P’s PID.
• Process C terminates automatically.
• Process P will not be allowed to exit until C exits.

```json
{
  "problem_id": "20",
  "points": 2,
  "type": "Freeform",
  "tags": ["os", "process-management", "fork"],
  "answer": "None of the listed statements are definitely true.",
  "llm_judge_instructions": "Award 2 points if the student correctly states that none of the listed statements are definitely true and provides a brief justification (one sentence) explaining why (e.g., PID reuse policy, child retains its own PID, child does not automatically terminate, parent can exit and become a zombie until reaped). Award 0 points otherwise."
}
```

---

## Question 21 [4 point(s)]

Consider a virtual memory system with 64-bit virtual addresses, and a page size of 32KB (2^15 bytes). The system uses multi-level paging. Each page table holds at most 2^13 entries, and each page table directory holds at most 2^12 entries. In the worst case, how many memory accesses are required to translate a virtual address to a physical address? (Assume a 4-level tree: 3 levels of directories plus a level of page tables.)

```json
{
  "problem_id": "21",
  "points": 4,
  "type": "Freeform",
  "tags": ["vm", "paging"],
  "answer": "4",
  "llm_judge_instructions": "Award 4 points if the student states that the worst-case number of memory accesses is 4 and gives a brief justification matching the 4 levels (3 directory lookups + 1 page table lookup). Award 0 points otherwise."
}
```

---