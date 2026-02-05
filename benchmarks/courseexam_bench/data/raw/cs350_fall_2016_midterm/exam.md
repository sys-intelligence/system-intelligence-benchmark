# CS350 Fall 2016 Midterm

```json
{
  "exam_id": "cs350_fall_2016_midterm",
  "test_paper_name": "CS350 Fall 2016 Midterm",
  "course": "CS350",
  "institution": "University of Waterloo",
  "year": 2016,
  "score_total": 50,
  "num_questions": 16
}
```

---

## Question 1a [2 point(s)]

a. (2 marks) List the semaphores that you will use in your solution. For each semaphore, state what its initial value should be.

```json
{
  "problem_id": "1a",
  "points": 2,
  "type": "Freeform",
  "tags": ["semaphores","concurrency"],
  "answer": "SemA: 2; SemB: 1",
  "llm_judge_instructions": "Award 2 points if both semaphores are listed with the correct initial values: SemA = 2 and SemB = 1. Award 0 points otherwise."
}
```

---

## Question 1b [8 point(s)]

b. (8 marks) Show the semaphore P and V operations that threads should perform before and after each call to funcA and funcB to enforce the synchronization requirements. Provide the exact sequence of P and V calls that each thread should execute around funcA and funcB.

```json
{
  "problem_id": "1b",
  "points": 8,
  "type": "Freeform",
  "tags": ["semaphores","concurrency"],
  "answer": "P(SemA); funcA(); V(SemA); P(SemB); P(SemA); funcB(); V(SemA); V(SemB)",
  "llm_judge_instructions": "Award 8 points for the exact sequence: P(SemA); funcA(); V(SemA); P(SemB); P(SemA); funcB(); V(SemA); V(SemB). Award 0 points for any other sequence."
}
```

---

## Question 2a [2 point(s)]

a. (2 marks) Suppose that each thread accesses the shared variable exactly one time, and that all k threads do so at exactly the same time, which we will refer to as time t = 0. At what time will the last of the threads finish releasing the spinlock?

```json
{
  "problem_id": "2a",
  "points": 2,
  "type": "Freeform",
  "tags": ["spinlocks","concurrency"],
  "answer": "t = 10k",
  "llm_judge_instructions": "Award 2 points for the answer 't = 10k'. Award 0 otherwise."
}
```

---

## Question 2b [2 point(s)]

b. (2 marks) For the same scenario described in part (a), what is the total amount of time that the threads will spend spinning? In other words, what is the sum of the threads’ spinning times?

```json
{
  "problem_id": "2b",
  "points": 2,
  "type": "Freeform",
  "tags": ["spinlocks","concurrency"],
  "answer": "Total spinning time = 10 * sum_{i=0}^{k-1} i = 5(k^2 - k)",
  "llm_judge_instructions": "Award 2 points for the correct closed-form expression for total spinning time (e.g., '5(k^2 - k)' or '10 * sum_{i=0}^{k-1} i'). Award 0 otherwise."
}
```

---

## Question 2c [2 point(s)]

c. (2 marks) For this part of the question, assume that there are k threads timesharing a single processor. The first thing that each thread does when it is able to run is to acquire the spinlock and access the shared variable. Each thread accesses the shared variable one time. Assume that the scheduling quantum is larger than 10 time units. What is the total amount of time that the threads will spend spinning?

```json
{
  "problem_id": "2c",
  "points": 2,
  "type": "Freeform",
  "tags": ["spinlocks","concurrency"],
  "answer": "0 (none of the threads will spin)",
  "llm_judge_instructions": "Award 2 points if the answer states that total spinning time is 0 and gives the brief justification that only one thread runs at a time and it acquires the lock without spinning. Award 0 otherwise."
}
```

---

## Question 3a [2 point(s)]

a. (2 marks) Assuming that no errors occur, are the following values for numbers possible after all threads have finished executing? For each, answer “Yes” or “No”, and give a brief (one sentence) explanation.
numbers[10] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0}

```json
{
  "problem_id": "3a",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency","memory-order"],
  "answer": "Yes. This could occur if every instance of myThreadB runs and exits before any myThreadA increments value.",
  "llm_judge_instructions": "Award 2 points for 'Yes' with a brief correct explanation (e.g., all B threads execute before any A increments). Award 0 otherwise."
}
```

---

## Question 3b [2 point(s)]

b. (2 marks) Repeat part (a), but for the following values for numbers:
numbers[10] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 12}

```json
{
  "problem_id": "3b",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency","memory-order"],
  "answer": "No. The value starts at 0 and can be incremented at most 10 times, so it cannot be 12.",
  "llm_judge_instructions": "Award 2 points for 'No' with the correct justification that the value cannot exceed 10 increments. Award 0 otherwise."
}
```

---

## Question 3c [2 point(s)]

c. (2 marks) Repeat part (a), but for the following values for numbers:
numbers[10] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}

```json
{
  "problem_id": "3c",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency","memory-order"],
  "answer": "Yes. This could occur if each pair myThreadA/myThreadB executes completely before the next myThreadA increments.",
  "llm_judge_instructions": "Award 2 points for 'Yes' with a brief correct justification. Award 0 otherwise."
}
```

---

## Question 3d [2 point(s)]

d. (2 marks) Repeat part (a), but for the following values for numbers:
numbers[10] = {9, 8, 7, 6, 5, 4, 3, 2, 1, 0}

```json
{
  "problem_id": "3d",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency","memory-order"],
  "answer": "Yes. This ordering can occur given appropriate interleaving of threads (e.g., B threads executing before their A increments and threads running in decreasing order).",
  "llm_judge_instructions": "Award 2 points for 'Yes' with a brief correct justification about possible thread interleavings. Award 0 otherwise."
}
```

---

## Question 4 [6 point(s)]

a. (2 marks) Process P calls the fork syscall and creates process C. Process P exits before process C exits. Assume that the kernel does not allow a process to call waitpid on any process except its children. Are any of the following statements definitely true at the time that P exits? Circle any that are true.
• Process P’s PID can be safely re-used by the kernel.
• Process C inherits process P’s PID.
• Process C terminates automatically.
• Process P will not be allowed to exit until C exits.

b. (4 marks) Consider a virtual memory system with 64-bit virtual addresses, and a page size of 32KB (2^15 bytes). The system uses multi-level paging. Each page table holds at most 2^13 entries, and each page table directory holds at most 2^12 entries. In the worst case, how many memory accesses are required to translate a virtual address to a physical address?

```json
{
  "problem_id": "4",
  "points": 6,
  "type": "Freeform",
  "tags": ["process","fork","virtual-memory","paging"],
  "answer": "Part (a): None of the listed statements are definitely true. Part (b): 4 memory accesses in the worst case.",
  "llm_judge_instructions": "Allocate points as follows: 2 points for Part (a) if the answer states that none of the statements is definitely true with brief justification; 4 points for Part (b) if the answer gives '4' (and a brief correct reasoning that the page table structure leads to four levels). Partial credit: for Part (b) up to 2 points for recognizing multiple-level translation and giving a plausible level count if not exactly 4."
}
```

---

## Question 5 [8 point(s)]

Draw the relevant stack frames for the application and kernel stacks for an OS161 process in the middle of calling fork. Assume that the parent process is in sys_fork (the kernel handler function for fork), and that the child process has been created and is about to call mips_usermode. Draw the stacks of both the parent and child processes showing the trap frame, syscall frames, and any frames that must be copied or adjusted.

```json
{
  "problem_id": "5",
  "points": 8,
  "type": "Freeform",
  "tags": ["os161","stacks","fork"],
  "answer": "Expected answer describes: parent kernel stack containing trap frame and sys_fork frames; child kernel stack containing a copied trap frame and a minimal kernel frame to return into user mode (e.g., enter_forked_process), and both application stacks arranged so the child will resume in user mode. The answer should indicate which frames are copied and which are unique to parent/child.",
  "llm_judge_instructions": "Award up to 8 points distributed as: 4 points for correctly drawing/identifying the parent stacks (kernel trap frame and sys_fork frames) and explaining their roles; 4 points for correctly drawing/identifying the child stacks (copied trap frame, entry frame such as enter_forked_process, and eventual user-mode context) and explaining which frames are copied vs new. Partial credit proportional to completeness and correctness of elements."
}
```

---

## Question 6a [3 point(s)]

a. (3 marks) On the MIPS, the load linked (ll) and store conditional (sc) instructions are used to implement spinlocks. Suppose that two threads, T1 and T2, try to acquire an unlocked spinlock at the same time, and that their ll and sc instructions execute in the following order:
T1: ll
T1: time passes
T2: ll
T1: sc
T2: sc
Which thread(s) will acquire the spinlock after this sequence? Answer one of: T1, T2, both, neither.

```json
{
  "problem_id": "6a",
  "points": 3,
  "type": "Freeform",
  "tags": ["mips","spinlock","llsc"],
  "answer": "T2",
  "llm_judge_instructions": "Award 3 points for answering 'T2' with brief justification that T1's sc will fail because T2's ll occurred after T1's ll, so T2's sc succeeds and T1's sc fails. Award 0 otherwise."
}
```

---

## Question 6b [3 point(s)]

b. (3 marks) Suppose that the MIPS spinlock was mistakenly implemented using a regular load instruction (lw, instead of ll) and a regular store instruction (sw, instead of sc). Suppose the instruction sequence is the same as in part (a):
T1: lw
T1: time passes
T2: lw
T1: sw
T2: sw
Which thread(s) will believe that they have acquired the spinlock after this sequence? Answer one of: T1, T2, both, neither.

```json
{
  "problem_id": "6b",
  "points": 3,
  "type": "Freeform",
  "tags": ["mips","spinlock","llsc"],
  "answer": "Both",
  "llm_judge_instructions": "Award 3 points for answering 'Both' with brief justification that without ll/sc atomicity both stores can succeed and both threads may believe they hold the lock. Award 0 otherwise."
}
```

---

## Question 7a [2 point(s)]

a. (2 marks) What is the difference between a thread yielding and a thread blocking?

```json
{
  "problem_id": "7a",
  "points": 2,
  "type": "Freeform",
  "tags": ["threads","scheduling"],
  "answer": "A yielding thread moves from running to ready and can be immediately scheduled again; a blocked thread is not runnable and waits for a resource, so it cannot be scheduled until unblocked.",
  "llm_judge_instructions": "Award 2 points for a correct distinction mentioning that yield makes the thread ready (runnable) while blocking makes it non-runnable and waiting for a resource. Award 0 otherwise."
}
```

---

## Question 7b [2 point(s)]

b. (2 marks) When an exception or interrupt occurs, a trap frame must be created to preserve the application’s context. This trap frame is put on a separate kernel stack, instead of the application’s stack: why? List the reasons why a kernel stack is used.

```json
{
  "problem_id": "7b",
  "points": 2,
  "type": "Freeform",
  "tags": ["traps","kernel"],
  "answer": "Because the user stack pointer is user-controlled and may be invalid, using a kernel stack protects kernel data from user access and avoids requiring the kernel to rely on user-space memory for kernel needs.",
  "llm_judge_instructions": "Award 2 points for mentioning that the user stack pointer may be invalid/untrusted and that using a kernel stack protects kernel data and avoids depending on user memory. Award partial credit for mentioning one of these reasons."
}
```

---

## Question 7c [2 point(s)]

c. (2 marks) Both wait channels and condition variables can be used to make threads block. How does wchan_sleep differ from cv_wait?

```json
{
  "problem_id": "7c",
  "points": 2,
  "type": "Freeform",
  "tags": ["wait-channel","condition-variable"],
  "answer": "wchan_sleep blocks the calling thread without automatically releasing or reacquiring a lock; cv_wait blocks and atomically releases the associated lock and reacquires it upon wakeup.",
  "llm_judge_instructions": "Award 2 points for correctly stating that cv_wait atomically releases and reacquires an associated lock while wchan_sleep does not manage a lock. Award 0 otherwise."
}
```

---