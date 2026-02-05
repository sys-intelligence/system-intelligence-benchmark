# CS 350 Winter 2019 Midterm

```json
{
  "exam_id": "cs350_winter_2019_midterm",
  "test_paper_name": "CS 350 Winter 2019 Midterm",
  "course": "CS 350",
  "institution": "University of Waterloo",
  "year": 2019,
  "score_total": 74,
  "num_questions": 26
}
```
---
## Question 1 [6 point(s)]

a.  (2 marks) Efficiency
Which is typically faster and why:
i) Printing the numbers from 1 to 1000000, one number at a time.
ii) Creating a string with the numbers from 1 to 1000000 and printing that string.

```json
{
  "problem_id": "1",
  "points": 2,
  "type": "Freeform",
  "tags": ["efficiency"],
  "answer": "ii (Creating a string and printing that string) is typically faster because it reduces the number of I/O/syscall operations by batching output.",
  "llm_judge_instructions": "Award 2 points for stating that (ii) is faster and giving a correct reason (e.g., fewer syscalls or less I/O overhead). Award 0 points otherwise."
}
```
---
b.  (2 marks) Concurrency
Can you still have concurrency if you have a single processor with a single core and the degree of multithreading is one (i.e., P=1, C=1, M=1)?

```json
{
  "problem_id": "2",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency"],
  "answer": "Yes. Preemption/time-sharing and I/O overlap can enable concurrency even on a single core.",
  "llm_judge_instructions": "Award 2 points for 'Yes' with justification mentioning preemption/timesharing or I/O concurrency enabling apparent simultaneous progress. Award 0 points for other answers."
}
```
---
c.  (2 marks) Synchronization
Can a lock be used anywhere a binary semaphore is used?

```json
{
  "problem_id": "3",
  "points": 2,
  "type": "Freeform",
  "tags": ["synchronization"],
  "answer": "No. A lock enforces ownership (only the acquiring thread should release), while a binary semaphore can be signaled by a different thread; thus locks are not interchangeable where cross-thread signaling is required.",
  "llm_judge_instructions": "Award 2 points for answering 'No' and explaining the ownership vs signaling difference (locks enforce owner-based release; semaphores can be signaled by other threads). Award 0 points otherwise."
}
```
---
## Question 2 [10 total marks]

a.  (2 marks) Concurrency
List two possible advantages of concurrency.

```json
{
  "problem_id": "4",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency"],
  "answer": "Improved CPU utilization; improved performance (through parallelism or overlap of I/O and computation).",
  "llm_judge_instructions": "Award 1 point for each distinct correct advantage up to 2 points (e.g., improved CPU utilization, better responsiveness, overlap of I/O and computation, improved throughput)."
}
```
---
b.  (4 marks) Context Switching
There are a number of ways that a context switch can occur.
i) Which ones are prevented when interrupts are turned off.
ii) Which ones are prevented when each process only has a single thread of execution.
iii) Which ones are not prevented by either of the two previous conditions.

```json
{
  "problem_id": "5",
  "points": 1,
  "type": "Freeform",
  "tags": ["context-switching"],
  "answer": "Preemption (i.e., interrupt-driven preemption) is prevented when interrupts are turned off.",
  "llm_judge_instructions": "Award 1 point for stating that interrupt-driven preemption is prevented when interrupts are disabled. Award 0 otherwise."
}
```
---
```json
{
  "problem_id": "6",
  "points": 1,
  "type": "Freeform",
  "tags": ["context-switching"],
  "answer": "None are prevented solely by each process having a single thread; thread-level switches within a process are not possible, but process switches and preemption can still occur.",
  "llm_judge_instructions": "Award 1 point for indicating that no additional types of context switch are universally prevented simply by having a single thread per process (explain briefly if desired). Award 0 otherwise."
}
```
---
```json
{
  "problem_id": "7",
  "points": 2,
  "type": "Freeform",
  "tags": ["context-switching"],
  "answer": "Actions not prevented by either condition include voluntary thread exit (threadexit), explicit yield (threadyield), and thread blocking/sleep.",
  "llm_judge_instructions": "Award 2 points for listing the three items (thread exit, thread yield, thread block/sleep) or equivalent. Award 1 point for listing two correct items. Award 0 points otherwise."
}
```
---
c.  (4 marks) cvwait
List, in order, the four steps of cv_wait. Do not list any of the KASSERTs.

1.
2.
3.
4.

```json
{
  "problem_id": "8",
  "points": 4,
  "type": "Freeform",
  "tags": ["cv-wait"],
  "answer": "1. wchan_lock(cv->wchan); 2. lock_release(lk); 3. wchan_sleep(cv->wchan); 4. lock_acquire(lk).",
  "llm_judge_instructions": "Award 4 points if all four steps are listed in the correct order. Partial credit: award 1 point per step that is correct and in the correct position, up to 4 points."
}
```
---
## Question 3 [14 total marks]

a.  (1 mark)
Under what case (or cases) does disabling interrupts enforce mutual exclusion.

```json
{
  "problem_id": "9",
  "points": 1,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "When there is a single core (a uniprocessor system); disabling interrupts prevents preemption on that core.",
  "llm_judge_instructions": "Award 1 point for stating that disabling interrupts enforces mutual exclusion on a single-core (uniprocessor) system. Award 0 otherwise."
}
```
---
b.  (1 mark)
Give one disadvantage of a scheduling quantum that is too short (i.e., 1ms or less).

```json
{
  "problem_id": "10",
  "points": 1,
  "type": "Freeform",
  "tags": ["scheduling"],
  "answer": "Excessive context-switch overhead leading to lower effective CPU throughput and poor cache performance.",
  "llm_judge_instructions": "Award 1 point for identifying an appropriate disadvantage such as excessive scheduler overhead or poor cache performance. Award 0 otherwise."
}
```
---
c.  (1 mark)
Give one disadvantage of a scheduling quantum that is too long (i.e., 1s or more).

```json
{
  "problem_id": "11",
  "points": 1,
  "type": "Freeform",
  "tags": ["scheduling"],
  "answer": "Poor responsiveness: threads respond to events slowly and the system may appear unresponsive to users.",
  "llm_judge_instructions": "Award 1 point for identifying reduced responsiveness or related disadvantage. Award 0 otherwise."
}
```
---
d.  (1 mark)
What do exceptions and interrupts have in common?

```json
{
  "problem_id": "12",
  "points": 1,
  "type": "Freeform",
  "tags": ["exceptions","interrupts"],
  "answer": "Both transfer control to the kernel (the kernel handles both).",
  "llm_judge_instructions": "Award 1 point for stating that both cause control to be transferred to kernel exception/interrupt handling. Award 0 otherwise."
}
```
---
e.  (1 mark)
What would be a scenario (if any) where a kernel stack would have a trapframe pushed and popped without a switchframe also being pushed and popped.

```json
{
  "problem_id": "13",
  "points": 1,
  "type": "Freeform",
  "tags": ["kernel-stack","interrupts"],
  "answer": "An interrupt (e.g., a timer interrupt or device interrupt) that is handled and returns without a thread context switch.",
  "llm_judge_instructions": "Award 1 point for citing an interrupt that is handled and returns (e.g., timer interrupt before quantum expires or device interrupt) causing only trapframe push/pop. Award 0 otherwise."
}
```
---
f.  (1 mark)
What would be a scenario (if any) where a kernel stack would have a switchframe pushed and popped without a trapframe also being pushed and popped.

```json
{
  "problem_id": "14",
  "points": 1,
  "type": "Freeform",
  "tags": ["kernel-stack","thread-yield"],
  "answer": "A voluntary thread yield (thread_yield) performed in kernel code that performs a context switch without an intervening trap/interrupt.",
  "llm_judge_instructions": "Award 1 point for identifying kernel-level thread yield (or similar kernel-invoked context switch) as the scenario. Award 0 otherwise."
}
```
---
g.  (1 mark)
Why can’t you have a pid of 0 in os/161?

```json
{
  "problem_id": "15",
  "points": 1,
  "type": "Freeform",
  "tags": ["os-161"],
  "answer": "Because fork returns 0 to the child, so 0 is used as the fork return value and cannot be a valid pid.",
  "llm_judge_instructions": "Award 1 point for the stated reason that pid 0 would conflict with fork's return value semantics. Award 0 otherwise."
}
```
---
h.  (2 marks)
A programmer is writing a program that requires two major (but independent) tasks to be performed and is trying to decide between using fork and assigning one task to the parent and one to the child or using thread_fork and assigning one task to each thread.
i) What would be one advantage of using fork?
ii) What would be one advantage of using thread_fork?

```json
{
  "problem_id": "16",
  "points": 2,
  "type": "Freeform",
  "tags": ["process-vs-thread"],
  "answer": "i) Fault isolation: a bug in one process will not corrupt the other process. ii) Threads use less memory and make sharing or communicating data between tasks easier.",
  "llm_judge_instructions": "Award 1 point for a correct advantage for (i) (e.g., fault isolation). Award 1 point for a correct advantage for (ii) (e.g., lower memory overhead or easier data sharing)."
}
```
---
i.  (3 total marks)
Draw the user and kernel stacks for a process that is executing sys_waitpid. Show the top of the stack (where items are pushed or popped) at the bottom of the diagram.

```json
{
  "problem_id": "17",
  "points": 3,
  "type": "Freeform",
  "tags": ["stacks-diagram"],
  "answer": "A diagram or description showing the user stack containing application frames (including the call to waitpid), and the kernel stack containing (from bottom/top): trapframe, mips trap/entry frame, syscall handling frames, and the kernel's waitpid handling frame. Indicate the top of stack at the bottom of the diagram.",
  "llm_judge_instructions": "Award up to 3 points: 1 point for correctly identifying the user-side call to waitpid on the user stack, 1 point for correctly listing kernel stack components including trapframe and syscall frames, and 1 point for correctly indicating top/bottom orientation. Partial credit as appropriate."
}
```
---
j.  (2 total marks)
Explain how the following kernel stack could come to be (two trapframes stacked): describe a plausible cause.

```json
{
  "problem_id": "18",
  "points": 2,
  "type": "Freeform",
  "tags": ["exception-handling"],
  "answer": "A bug in commonexception that enabled interrupts before mipstrap was called could allow an interrupt to occur while already handling an exception, causing nested trapframes.",
  "llm_judge_instructions": "Award 2 points for identifying the cause (e.g., enabling interrupts prematurely in exception handling leading to nested trapframes). Award 0 otherwise."
}
```
---
## Question 4 [10 marks]

The following pseudocode makes use of a semaphore. Replace the semaphore-based implementation with a condition-variable-based implementation that performs the same task. You may only add up to three additional variables. Your cv may not be used with a loop.

Semaphore barrier; // initialized to 0

(intended behavior: threads call CS350/KernelFunction, signal the barrier; main waits for NUMTHREADS signals then proceeds to MarkMidterms/continue.)

Provide a cv-based implementation that matches semaphore semantics (no loop in cv_wait usage).

```json
{
  "problem_id": "19",
  "points": 10,
  "type": "Freeform",
  "tags": ["cv-wait"],
  "answer": "Provide a CV-based barrier: declare int count = 0; lock countLock; cv barrier; in thread: acquire(countLock); count++; if (count == NUMTHREADS) cv_signal(countLock, barrier); release(countLock); in main: acquire(countLock); if (count != NUMTHREADS) cv_wait(countLock, barrier); release(countLock); Ensure no loops are used in cv_wait per constraint.",
  "llm_judge_instructions": "Award points as follows (total 10): 1 point for declaring the counter variable, 1 point for declaring the lock, 1 point for declaring the CV, 1 point for acquiring the lock before increment, 1 point for incrementing the counter, 1 point for signaling when count equals NUMTHREADS, 1 point for main acquiring the lock before checking count, 1 point for main performing cv_wait when count != NUMTHREADS, 1 point for releasing the lock in main after wait, and 1 point for obeying the constraint of not using a loop for cv_wait and overall correctness. Partial credit allowed per item."
}
```
---
## Question 5 [10 marks]

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
(b) If you answered no to (a), correct the code (you may edit the code in-place).
(c) If there are any other issues with the lock not related to mutual exclusion, correct them. Otherwise, indicate the implementation is correct.

Provide corrected code and explanation.

```json
{
  "problem_id": "20",
  "points": 10,
  "type": "Freeform",
  "tags": ["locks","mutual-exclusion"],
  "answer": "a) No. The release uses V on the semaphore at the start and twice, which is incorrect, and there are missing wake-ups. b) Corrected approach: use P(lk->sem) to enter critical sections of the lock's internal state and V(lk->sem) when done; on release, set owner=NULL while holding lk->sem and then wake one waiter via wchan_wakeone before V(lk->sem). Also assert ownership in release. c) Add KASSERT(lk->owner == curthread) in release and use wchan_wakeone to wake sleepers.",
  "llm_judge_instructions": "Award points as follows (total 10): 2 points for correctly stating that the original code does not guarantee mutual exclusion and why; 4 points for providing a correct corrected code snippet that (i) uses the semaphore correctly (P/V) around updates, (ii) sets owner appropriately, and (iii) wakes waiters (e.g., wchan_wakeone); 4 points for identifying and fixing other issues (ownership assertions, correct ordering of P/V, and proper wake semantics). Partial credit as appropriate."
}
```
---
## Question 6 [8 marks]

A system uses segmented address space for its implementation of virtual memory. Suppose a process initially uses 48KB of memory for its heap. The process then runs low on heap space and requests 16 KB more space. Assume you have access to a procedure sbrk and that sbrk(16*1024) will request that the heap’s space be increased by 16 KB by finding a new location in RAM for the heap segment. If successful it returns the new address, otherwise it returns NULL.

In roughly 4–6 steps, describe the process that would be required to increase the process’s address space.

```json
{
  "problem_id": "21",
  "points": 8,
  "type": "Freeform",
  "tags": ["virtual-memory","sbrk"],
  "answer": "Suggested steps: (1) Check if there is enough physical/virtual space to allocate a new heap region; if not, return ENOMEM. (2) Allocate a new heap region of the larger size (or find new location). (3) Copy the contents of the old heap to the new region. (4) Update the process's heap relocation/base and limit/size in the kernel data structures. (5) Update MMU mappings for the new heap region. (6) Free or release the old heap region.",
  "llm_judge_instructions": "Award up to 8 points distributed roughly as: 1 point for checking space, 1 point for returning ENOMEM if insufficient, 1 point for allocating the new region, 2 points for copying old heap contents correctly, 1 point for updating kernel-side relocation/limit, 1 point for updating MMU mappings, and 1 point for releasing the old heap. Partial credit for partially correct sequences."
}
```
---
## Question 7 [8 total marks]

A system uses 24-bit virtual addresses, 24-bit physical addresses and memory segmentation. There are four segments and two bits are used for the segment number. The relocation and limit for each of the segments are as follows.

Segment Number | Limit Register | Relocation Register
0x0 | 0x2 0000 | 0x40 0000
0x1 | 0xC 0000 | 0x70 0000
0x2 | 0x9 0000 | 0x50 0000
0x3 | 0xA 0000 | 0x60 0000

Translate the following addresses from virtual to physical. Clearly indicate what segment each address belongs to.

a.  (2 marks) 0x01D0D4

b.  (2 marks) 0x22CA10

c.  (2 marks) 0x3347B8

d.  (2 marks) 0x1CF008

```json
{
  "problem_id": "22",
  "points": 8,
  "type": "Freeform",
  "tags": ["segmentation","virtual-memory"],
  "answer": "a) Virtual 0x01D0D4: segment 0x0, offset 0x1D0D4 -> physical 0x401D0D4 (if offset < limit). b) 0x22CA10: segment 0x2, offset 0x2CA10 -> check offset against limit; if offset exceeds limit, segmentation violation; otherwise add relocation. c) 0x3347B8: segment 0x3, offset 0x347B8 -> check offset vs limit; if offset exceeds limit, segmentation violation. d) 0x1CF008: segment 0x1, offset 0xCF008 -> check offset vs limit; if offset exceeds limit, segmentation violation.",
  "llm_judge_instructions": "Award 2 points for each part: for (a) correct segment and correct translated physical address; for (b)-(d) award 2 points if the student correctly identifies the segment and either computes the correct physical address or correctly states that the access is a segmentation violation because the offset exceeds the limit. Partial credit as appropriate."
}
```
---
## Question 8 [8 total marks]

Ideally any scheme to enforce mutual exclusion should satisfy the following constraints.
i. Only one thread is allowed in a critical section at a time.
ii. No assumptions can be made about the order different threads will access the critical section.
iii. A thread that is outside the critical section cannot prevent another thread from entering the critical section.
iv. At least one thread should be making progress.
v. There should be a bound on the time a thread must wait.

For each of four cases listed below there are only two threads, T1 and T2. Rather than use locks, the threads use the code below to provide mutual exclusion to a critical region. Each thread will be trying to access the critical region multiple times (i.e., not just once). For each case state whether the scheme meets all the requirements; if not, state which requirement is violated and give a scenario.

a.  (2 marks)

#define CLOSED 0
#define OPEN   1
volatile int Lock = OPEN; // global variable

AccessCriticalRegion() {
  while (Lock == CLOSED) {;} // busy wait
  Lock = CLOSED;
  CriticalSection();
  Lock = OPEN;
}

```json
{
  "problem_id": "23",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "This scheme does not meet all requirements. It can break mutual exclusion (i) because the test and set are not atomic: thread A can read Lock==OPEN, be preempted before setting it, and thread B can enter the critical section.",
  "llm_judge_instructions": "Award 2 points for identifying violation of (i) and giving the race scenario (read-then-interrupt then other thread enters). Award 0 otherwise."
}
```
---
b.  (2 marks)

volatile int Last = 2; // global variable

T1AccessCriticalRegion() {
  while (Last == 1){;}
  CriticalSection();
  Last = 1;
}

T2AccessCriticalRegion() {
  while (Last == 2){;}
  CriticalSection();
  Last = 2;
}

```json
{
  "problem_id": "24",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "This scheme can violate requirement (iii): a thread outside the critical section can prevent the other from entering. For example, if Last==1 and T1 is not in the critical section but Last remains 1, T1 may be prevented from entering even though T2 is not inside.",
  "llm_judge_instructions": "Award 2 points for identifying the violated constraint (iii) with an appropriate scenario. Partial credit for pointing out issues with ordering assumptions (ii)."
}
```
---
c.  (2 marks)

#define WANT_IN 1
volatile int T1 = !WANT_IN; // global variables
volatile int T2 = !WANT_IN;

T1AccessCriticalRegion() {
  T1 = WANT_IN;
  while (T2 == WANT_IN){;}
  CriticalSection();
  T1 = !WANT_IN;
}

T2AccessCriticalRegion() {
  T2 = WANT_IN;
  while (T1 == WANT_IN){;}
  CriticalSection();
  T2 = !WANT_IN;
}

```json
{
  "problem_id": "25",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "This scheme can violate (iv) progress (deadlock/starvation). Both threads can set their WANT_IN flag and then spin waiting for the other, resulting in no thread making progress.",
  "llm_judge_instructions": "Award 2 points for identifying the progress/deadlock issue (iv) and describing the scenario where both set their flags and wait. Award 0 otherwise."
}
```
---
d.  (2 marks)

#define WANT_IN 1
volatile int T1 = !WANT_IN; // global variables
volatile int T2 = !WANT_IN;
volatile int Last = 1;

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
  "problem_id": "26",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "This is a correct mutual exclusion algorithm for two threads (a variant of Peterson-like algorithm); it meets the listed requirements for two threads.",
  "llm_judge_instructions": "Award 2 points if the student correctly states that the scheme works (and optionally provides a brief justification such as bounded wait and mutual exclusion reasoning). Award 0 otherwise."
}
```
---