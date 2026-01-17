# CS350 Winter 2019 Midterm

```json
{
  "exam_id": "cs350_winter_2019_midterm",
  "test_paper_name": "CS350 Winter 2019 Midterm",
  "course": "CS350",
  "institution": "University of Waterloo",
  "year": 2019,
  "score_total": 63,
  "num_questions": 29
}
```

---

## Question 1 [6 point(s)]

1. (6 total marks)
For the following questions provide an answer and then justify your answer with a single sentence.
a. (2 marks) Efficiency
Which is typically faster and why:
i Printing the numbers from 1 to 1000000, one number at a time.
ii Creating a string with the numbers from 1 to 1000000 and printing that string.

b. (2 marks) Concurrency
Can you still have concurrency if you have a single processor with a single core and the degree of multithreading is one (i.e. P=1, C=1, M=1)?

c. (2 marks) Synchronization
Can a lock be used anywhere a binary semaphore is used?

```json
{
  "problem_id": "1a",
  "points": 2,
  "type": "Freeform",
  "tags": ["efficiency"],
  "answer": "Creating a string and printing it is typically faster.",
  "llm_judge_instructions": "Award 1 point for correctly identifying that creating a string and printing it (option ii) is faster. Award 1 point for a correct justification stating that printing one number at a time incurs many system calls or many small I/O operations, whereas creating one large string reduces system calls / I/O overhead."
}
```

```json
{
  "problem_id": "1b",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency"],
  "answer": "No.",
  "llm_judge_instructions": "Award 1 point for answering 'No'. Award 1 point for a correct brief justification: with only a single thread of execution on a single core there is no concurrent execution of multiple tasks (only sequential execution / interleaving is possible)."
}
```

```json
{
  "problem_id": "1c",
  "points": 2,
  "type": "Freeform",
  "tags": ["synchronization"],
  "answer": "No.",
  "llm_judge_instructions": "Award 1 point for answering 'No'. Award 1 point for a correct justification: explain a situation where a binary semaphore is used for signaling (e.g., between interrupt handler and thread) or where ownership semantics differ (locks enforce ownership and sleeping behavior), so a lock cannot always substitute for a binary semaphore."
}
```

---

## Question 2 [10 point(s)]

2. (10 total marks) For the following questions point form answers are preferred.
a. (2 marks) Concurrency
List two possible advantages of concurrency.

b. (4 marks) Context Switching
There are a number of ways that a context switch can occur.
i Which ones are prevented when interrupts are turned off.
ii Which ones are prevented when each process only has a single thread of execution.
iii Which ones are not prevented by either of the two previous conditions.

c. (4 marks) cvwait
List, in order, the four steps of cv_wait. Do not list any of the KASSERTs.
1.
2.
3.
4.
```json
{
  "problem_id": "2a",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency"],
  "answer": "Examples: improved CPU utilization (overlap of computation and I/O); improved responsiveness for interactive tasks.",
  "llm_judge_instructions": "Award 1 point for each distinct valid advantage listed (up to 2 points). Accept common valid answers such as improved CPU utilization, better throughput, improved responsiveness, increased resource utilization, overlapping I/O and computation."
}
```

```json
{
  "problem_id": "2b_i",
  "points": 1,
  "type": "Freeform",
  "tags": ["context-switching", "interrupts"],
  "answer": "Preemption (timer-driven interrupt-based preemption) is prevented when interrupts are disabled.",
  "llm_judge_instructions": "Award 1 point if the student identifies that interrupt-driven preemption (e.g., timer interrupts causing a context switch) is prevented when interrupts are turned off. Partial synonyms (timer preemption, interrupt-driven scheduling) are acceptable."
}
```

```json
{
  "problem_id": "2b_ii",
  "points": 1,
  "type": "Freeform",
  "tags": ["context-switching", "threads"],
  "answer": "Thread-level context switches within the same process (intra-process thread switching) are prevented; only process-level switches remain.",
  "llm_judge_instructions": "Award 1 point if the student states that intra-process thread switches are prevented (i.e., no switching between multiple threads of the same process), or if they justify 'none' by explaining that only process-level context switches remain. Accept equivalent explanations."
}
```

```json
{
  "problem_id": "2b_iii",
  "points": 2,
  "type": "Freeform",
  "tags": ["context-switching", "threads"],
  "answer": "Context switches caused by voluntary thread actions remain possible: thread exit, thread yield, thread block/sleep.",
  "llm_judge_instructions": "Award 2 points for listing the context switches not prevented by either condition (voluntary thread exit, threadyield, or explicit blocking/sleep). Award 1 point if the student lists two of these correctly. Award 0 if fewer or incorrect items."
}
```

```json
{
  "problem_id": "2c",
  "points": 4,
  "type": "Freeform",
  "tags": ["cvwait"],
  "answer": "1) acquire lock associated with the cv; 2) release the lock and atomically go to sleep on the CV's wait channel; 3) sleep until signalled; 4) reacquire the lock before returning.",
  "llm_judge_instructions": "Award 1 point for each correct step in the correct order (4 steps total). Accept equivalent phrasing that preserves the order and semantics: (1) acquire lock, (2) release lock and enqueue on cv/wchan, (3) sleep/wait until signalled, (4) reacquire lock on wake."
}
```

---

## Question 3 [11 point(s)]

3. (11 total marks) For the following questions a single sentence answer will suffice.
a. (1 mark)
Under what case (or cases) does disabling interrupts enforce mutual exclusion.

b. (1 mark)
Give one disadvantage of a scheduling quantum that is too short (i.e., 1ms or less).

c. (1 mark)
Give one disadvantage of a scheduling quantum that is too long (i.e., 1s or more).

d. (1 mark)
What do exceptions and interrupts have in common?

e. (1 mark)
What would be a scenario (if any) where a kernel stack would have a trapframe pushed and popped without a switchframe also being pushed and popped.

f. (1 mark)
What would be a scenario (if any) where a kernel stack would have a switchframe pushed and popped without a trapframe also being pushed and popped.

g. (1 mark)
Why can’t you have a pid of 0 in os/161?

h. (2 marks)
A programmer is writing a program that requires two major (but independent) tasks to be performed and is trying to decide between
• using fork and assigning one task to the parent and one to the child or
• using threadfork and assigning one task to each thread.
i What would be one advantage of using fork?
ii What would be one advantage of using threadfork?

i. (0 marks)
Draw the user and kernel stacks for a process that is executing sys_waitpid. Show the top of the stack (where items are pushed on or popped off) at the bottom of the diagram. (This diagram question is omitted from the autograded file.)

j. (2 marks)
Explain how the following kernel stack (two trapframes) could come to be:
trapframe
trapframe

```json
{
  "problem_id": "3a",
  "points": 1,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "Disabling interrupts enforces mutual exclusion when there is only a single processor/core (so no other CPU can run) and the critical region is short and in kernel context.",
  "llm_judge_instructions": "Award 1 point for stating that disabling interrupts enforces mutual exclusion on a uniprocessor (single core) or otherwise explaining that it prevents preemption by interrupts on the same CPU."
}
```

```json
{
  "problem_id": "3b",
  "points": 1,
  "type": "Freeform",
  "tags": ["scheduling"],
  "answer": "A very short quantum increases context-switch overhead, reducing useful CPU time for each thread.",
  "llm_judge_instructions": "Award 1 point for stating a valid disadvantage such as increased scheduling overhead or reduced throughput due to excessive context switching."
}
```

```json
{
  "problem_id": "3c",
  "points": 1,
  "type": "Freeform",
  "tags": ["scheduling"],
  "answer": "A very long quantum reduces responsiveness and can make interactive tasks feel sluggish.",
  "llm_judge_instructions": "Award 1 point for stating a valid disadvantage such as poor responsiveness or long wait times for interactive tasks."
}
```

```json
{
  "problem_id": "3d",
  "points": 1,
  "type": "Freeform",
  "tags": ["exceptions", "interrupts"],
  "answer": "Both transfer control to the kernel (the processor/vectoring to kernel code to handle an event).",
  "llm_judge_instructions": "Award 1 point for stating that both cause control to transfer to kernel handler code (or equivalent)."
}
```

```json
{
  "problem_id": "3e",
  "points": 1,
  "type": "Freeform",
  "tags": ["kernel-stack"],
  "answer": "An interrupt that is handled and returns without a context switch; the trapframe is pushed and popped on the same kernel stack with no switchframe because no thread switch occurred.",
  "llm_judge_instructions": "Award 1 point for describing a scenario where an interrupt/trap is handled entirely on the current CPU without performing a thread context switch (so only trapframe push/pop occurs)."
}
```

```json
{
  "problem_id": "3f",
  "points": 1,
  "type": "Freeform",
  "tags": ["kernel-stack"],
  "answer": "A voluntary context switch in kernel code (e.g., thread_yield or thread_exit) where the kernel switches threads without an intervening trap from user mode.",
  "llm_judge_instructions": "Award 1 point for describing a context switch performed by the kernel (e.g., thread_yield) that pushes/pops a switchframe without a trapframe."
}
```

```json
{
  "problem_id": "3g",
  "points": 1,
  "type": "Freeform",
  "tags": ["os161"],
  "answer": "Because fork uses the return value 0 to indicate execution in the child, pid 0 would conflict with that convention and is therefore not a valid pid.",
  "llm_judge_instructions": "Award 1 point for explaining that pid 0 is not used because fork returns 0 to the child or otherwise stating the conflict/reserved nature of pid 0 in os/161."
}
```

```json
{
  "problem_id": "3h_i",
  "points": 1,
  "type": "Freeform",
  "tags": ["fork-vs-threadfork"],
  "answer": "Using fork isolates faults: a crash in the child does not affect the parent.",
  "llm_judge_instructions": "Award 1 point for stating a valid advantage of fork such as fault isolation or separate address spaces."
}
```

```json
{
  "problem_id": "3h_ii",
  "points": 1,
  "type": "Freeform",
  "tags": ["fork-vs-threadfork"],
  "answer": "Using threadfork uses less memory and allows easier sharing of data between tasks.",
  "llm_judge_instructions": "Award 1 point for stating a valid advantage of threads such as lower memory overhead or easier shared-memory communication."
}
```

```json
{
  "problem_id": "3j",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-stack"],
  "answer": "A bug allowed interrupts to be enabled while already handling an interrupt, causing a nested trap: the first trap pushed a trapframe, then the second trap pushed another trapframe; no context switch occurred.",
  "llm_judge_instructions": "Award 1 point for identifying that nested interrupts/traps occurred (two traps) and 1 point for explaining that interrupts were enabled prematurely (or equivalent) causing a second trapframe to be pushed without a switchframe."
}
```

---

## Question 4 [10 point(s)]

4. (10 marks)
The following pseudocode makes use of a semaphore. Replace the semaphore-based implementation with a condition-variable-based implementation that performs the same task. You may only add up to three additional variables. Your cv usage may not be inside a loop. Provide code (or clear pseudocode) for the per-thread function and for main showing initialization and waiting/signalling.

```json
{
  "problem_id": "4",
  "points": 10,
  "type": "Freeform",
  "tags": ["cv-wait", "synchronization"],
  "answer": "",
  "llm_judge_instructions": "Award up to 10 points total as follows: 3 points for declaring and initializing up to three additional variables correctly (e.g., int count=0; struct lock *countLock; struct cv *barrierCV) with initial values; 4 points for correct per-worker thread code: acquire lock, increment count, if count == NUMTHREADS then cv_signal (or cv_broadcast) while holding lock, release lock — credit for correct order and atomicity (1 point each for acquire, increment, conditional signal, release). 3 points for correct main thread code: acquire lock, if count != NUMTHREADS then cv_wait (with correct use of lock and cv), release lock, then proceed to MarkMidterms. Do not award points if a loop is used with the cv; require correct atomic sequencing and no busy-waiting. Accept equivalent correct implementations that use cv_signal vs cv_broadcast appropriately."
}
```

---

## Question 5 [2 point(s)]

5. (2 marks)
Consider the following implementation of a lock. Assume that sem is created with an initial count of 1.
lock_acquire( lock * lk )
{
KASSERT( lk != NULL );
P( lk->sem );
while ( lk->owner != NULL )
{
wchan_lock( lk->wchan );
V( lk->sem );
wchan_sleep( lk->wchan );
P( lk->sem );
}
lk->owner = curthread;
V( lk->sem );
}
lock_release( lock * lk )
{
KASSERT( lk != NULL );
V( lk->sem );
lk->owner = NULL;
V( lk->sem );
}
(a) If this lock was used to protect a critical section, would it guarantee mutual exclusion?
(b) If you answered yes to (a), why? If you answered no to (a), correct the code (you may edit the code in-place).
(c) If there are any other issues with the lock not related to mutual exclusion, correct them. Otherwise, indicate the implementation is correct.

```json
{
  "problem_id": "5_a",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion", "lock"],
  "answer": "No.",
  "llm_judge_instructions": "Award 1 point for answering 'No'. Award 1 point for a concise explanation of why mutual exclusion is not guaranteed (e.g., the unlock code does V twice and sets owner = NULL between V calls, allowing another thread to proceed when owner is inconsistent; or describe the race between V and owner update)."
}
```

---

## Question 6 [8 point(s)]

6. (8 marks)
A system uses segmented address space for its implementation of virtual memory. Suppose a process initially uses 48KB of memory for its heap. The process then runs low on heap space and requests 16 KB more space. Assume you have access to a procedure sbrk and that sbrk(16*1024) will request that the heap’s space be increased by 16 KB by finding a new location in RAM for the heap segment. If successful it returns the new address, otherwise it returns NULL.

In roughly 4–6 steps, describe the process that would be required to increase the process’s address space using relocation (sbrk that moves the segment). Describe key actions such as checking for space, allocation, copying, and updating kernel and MMU state.

```json
{
  "problem_id": "6",
  "points": 8,
  "type": "Freeform",
  "tags": ["memory-management", "sbrk", "segmentation"],
  "answer": "",
  "llm_judge_instructions": "Award up to 8 points distributed across the expected steps (4–6 steps). Suggested allocation: 1 point for step 1 (check available memory and return ENOMEM if insufficient), 2 points for step 2 (allocate a new heap region of requested size in physical memory), 2 points for step 3 (copy old heap contents to new region correctly), 1 point for step 4 (update the process's segment relocation and limit fields in the kernel), 1 point for step 5 (update MMU/segmentation registers or page tables to reflect new mapping), and 1 point for step 6 (free or delete old heap region). Accept equivalent step decompositions; award partial credit for partially correct sequences. Total must not exceed 8 points."
}
```

---

## Question 7 [8 point(s)]

7. (8 total marks)
A system uses 24-bit virtual addresses, 24-bit physical addresses and memory segmentation. There are four segments and two bits are used for the segment number. The relocation and limit for each of the segments are as follows.

Segment Number | Limit Register | Relocation Register
0x0 | 0x2 0000 | 0x40 0000
0x1 | 0xC 0000 | 0x70 0000
0x2 | 0x9 0000 | 0x50 0000
0x3 | 0xA 0000 | 0x60 0000

Translate the following addresses from virtual to physical. Clearly indicate what segment each address belongs to. If the offset exceeds the segment limit, state 'segmentation violation'.

a. (2 marks) 0x01D0D4

b. (2 marks) 0x22CA10

c. (2 marks) 0x3347B8

d. (2 marks) 0x1CF008

```json
{
  "problem_id": "7_a",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "segmentation"],
  "answer": "",
  "llm_judge_instructions": "Award 1 point for correctly identifying the segment number (top 2 bits) and 1 point for the correct physical address translation (relocation + offset) or for correctly stating 'segmentation violation' if the offset >= limit. Accept hexadecimal arithmetic answers. Provide full credit only if both parts are correct."
}
```

```json
{
  "problem_id": "7_b",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "segmentation"],
  "answer": "",
  "llm_judge_instructions": "Award 1 point for correct segment number identification and 1 point for correct physical translation or correct identification of a segmentation violation. Accept equivalent correct arithmetic and notation."
}
```

```json
{
  "problem_id": "7_c",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "segmentation"],
  "answer": "",
  "llm_judge_instructions": "Award 1 point for correct segment number and 1 point for correct translation or segmentation violation determination. Ensure the student used the limit registers to check for violation."
}
```

```json
{
  "problem_id": "7_d",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "segmentation"],
  "answer": "",
  "llm_judge_instructions": "Award 1 point for correct segment number identification and 1 point for correct physical address translation or correct 'segmentation violation' response. Partial credit possible for correct segment but incorrect offset arithmetic."
}
```

---

## Question 8 [8 point(s)]

8. (8 total marks)
Ideally any scheme to enforce mutual exclusion should satisfy the following constraints.
i. Only one thread is allowed in a critical section at a time.
ii. No assumptions can be made about the order different threads will access the critical section.
iii. A thread that is outside the critical section cannot prevent another thread from entering the critical section.
iv. At least one thread should be making progress.
v. There should be a bound on the time a thread must wait.

For each of four cases listed below there are only two threads, T1 and T2. Rather than use locks, the threads use the code below to provide mutual exclusion to a critical region. Each thread will be trying to access the critical region multiple times (i.e. not just once). For each subpart state whether the scheme meets all requirements; if not, identify which requirement is violated and give a scenario where it is not satisfied.

a. (2 marks) Both threads execute the same function.
#define CLOSED 0
#define OPEN   1
volatile int Lock = OPEN; // global variable
AccessCriticalRegion() {
  while (Lock == CLOSED) {;} // busy wait
  Lock = CLOSED;
  CriticalSection();
  Lock = OPEN;
}

b. (2 marks) Threads use different functions.
volatile int Last = 2; // global variable
// Code for T1
T1AccessCriticalRegion() {
  while (Last == 1){;}
  CriticalSection();
  Last = 1;
}
// Code for T2
T2AccessCriticalRegion() {
  while (Last == 2){;}
  CriticalSection();
  Last = 2;
}

c. (2 marks) Two-thread alternation with WANT_IN flags.
#define WANT_IN 1
volatile int T1 = !WANT_IN; // global variables
volatile int T2 = !WANT_IN;
// Code for T1
T1AccessCriticalRegion() {
  T1 = WANT_IN;
  while (T2 == WANT_IN){;}
  CriticalSection();
  T1 = !WANT_IN;
}
// Code for T2
T2AccessCriticalRegion() {
  T2 = WANT_IN;
  while (T1 == WANT_IN){;}
  CriticalSection();
  T2 = !WANT_IN;
}

d. (2 marks) Peterson-like algorithm (with Last variable).
#define WANT_IN 1
volatile int T1 = !WANT_IN; // global variables
volatile int T2 = !WANT_IN;
volatile int Last = 1;
// Code for T1
T1AccessCriticalRegion() {
  while (1) {
    T1 = WANT_IN;
    if (T2 == !WANT_IN) {
      break;
    }
    if (Last == 1) {
      T1 = !WANT_IN;
      while (Last == 1){;}
    }
  }
  CriticalSection();
  Last = 1;
  T1 = !WANT_IN;
}
// Code for T2
T2AccessCriticalRegion() {
  while (1) {
    T2 = WANT_IN;
    if (T1 == !WANT_IN) {
      break;
    }
    if (Last == 2) {
      T2 = !WANT_IN;
      while (Last == 2){;}
    }
  }
  CriticalSection();
  Last = 2;
  T2 = !WANT_IN;
}

```json
{
  "problem_id": "8_a",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion", "busy-wait"],
  "answer": "",
  "llm_judge_instructions": "Award 2 points if the student identifies that requirement (i) (mutual exclusion) is not satisfied and provides a scenario showing a race (e.g., both see Lock == OPEN and both enter) or identifies lack of atomic test-and-set. Award 1 point for partially correct identification (e.g., names the wrong requirement but describes a relevant race)."
}
```

```json
{
  "problem_id": "8_b",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion", "alternation"],
  "answer": "",
  "llm_judge_instructions": "Award 2 points if the student identifies that requirement (iii) (a thread outside the critical section cannot prevent another) is violated and gives a clear scenario (e.g., Last set to 1 prevents T1 from entering even if T2 is not in CS). Award 1 point for partially correct identification or incomplete scenario."
}
```

```json
{
  "problem_id": "8_c",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion", "deadlock"],
  "answer": "",
  "llm_judge_instructions": "Award 2 points if the student identifies that requirement (iv) (progress/avoid deadlock) can be violated and provides a scenario such as both threads set their WANT_IN simultaneously causing both to spin forever (deadlock). Award 1 point for partial explanation or identification of livelock/deadlock potential."
}
```

```json
{
  "problem_id": "8_d",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion", "peterson"],
  "answer": "",
  "llm_judge_instructions": "Award 2 points if the student states that this Peterson-like scheme meets the listed requirements and provides a brief justification (e.g., mutual exclusion via Last + flags, progress and bounded waiting arguments). If the student finds a subtle flaw, award points according to their correctness: 1 point for recognizing correct requirement satisfaction but weak justification."
}
```

---