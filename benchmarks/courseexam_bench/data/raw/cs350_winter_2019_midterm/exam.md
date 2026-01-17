# CS 350 Winter 2019 Midterm

```json
{
  "exam_id": "cs350_winter_2019_midterm",
  "test_paper_name": "CS 350 Winter 2019 Midterm",
  "course": "CS 350",
  "institution": "University of Waterloo",
  "year": 2019,
  "score_total": 74,
  "num_questions": 8
}
```

---

## Question 1 [6 point(s)]

For the following questions provide an answer and then justify your answer with a single sentence.

a.  (2 marks) Efficiency
Which is typically faster and why:
i) Printing the numbers from 1 to 1000000, one number at a time.
ii) Creating a string with the numbers from 1 to 1000000 and printing that string.

```json
{
  "problem_id": "1a",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency","synchronization"],
  "answer": "Creating a single large string and printing it is typically faster because it reduces system calls (one print vs one million).",
  "llm_judge_instructions": "Award 2 points if the student correctly states that option (ii) is faster and justifies that it reduces system calls (one print vs ~1,000,000 prints). Award 1 point if the student correctly identifies (ii) without a clear justification. 0 points otherwise."
}
```

b.  (2 marks) Concurrency
Can you still have concurrency if you have a single processor with a single core and the degree of multithreading is one (i.e., P=1, C=1, M=1)?

```json
{
  "problem_id": "1b",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency"],
  "answer": "Yes; concurrency (interleaving) can still be observed via preemption/time-slicing even on a single-core system.",
  "llm_judge_instructions": "Award 2 points if the student answers 'Yes' and explains that preemption/time-slicing or the scheduler can produce interleaved execution. Award 1 point if the student answers 'Yes' but gives an imprecise justification. 0 points for 'No' or unrelated answers."
}
```

c.  (2 marks) Synchronization
Can a lock be used anywhere a binary semaphore is used?

```json
{
  "problem_id": "1c",
  "points": 2,
  "type": "Freeform",
  "tags": ["synchronization","locks","semaphores"],
  "answer": "No; locks (mutexes) require acquire-before-release by the same thread, whereas binary semaphores allow P/V operations in different orders/contexts.",
  "llm_judge_instructions": "Award 2 points if the student states 'No' and explains that locks require the same thread to acquire and release while semaphores allow P/V in different orders or different contexts. Award 1 point for stating 'No' with a partial explanation. 0 points otherwise."
}
```

---

## Question 2 [10 point(s)]

For the following questions point form answers are preferred.

a.  (2 marks) Concurrency
List two possible advantages of concurrency.

```json
{
  "problem_id": "2a",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency","design"],
  "answer": "Examples: improved CPU utilization; improved responsiveness or throughput.",
  "llm_judge_instructions": "Award 1 point for each distinct valid advantage up to 2 points (e.g., improved CPU utilization, increased throughput, better responsiveness, overlapping I/O and computation)."
}
```

b.  (4 marks) Context Switching
There are a number of ways that a context switch can occur.
i) Which ones are prevented when interrupts are turned off?
ii) Which ones are prevented when each process only has a single thread of execution?
iii) Which ones are not prevented by either of the two previous conditions?

```json
{
  "problem_id": "2b",
  "points": 4,
  "type": "Freeform",
  "tags": ["context-switch","os"],
  "answer": "i) Preemption by interrupts is prevented. ii) With single-threaded processes, thread-to-thread context switches within the same process are not applicable (so none of those). iii) Voluntary context switches such as thread exit, thread yield, or blocking (sleep) are not prevented.",
  "llm_judge_instructions": "Award 1 point for correctly identifying (i) that preemption by interrupts is prevented. Award 1 point for (ii) correctly noting that single-threaded processes do not allow intra-process thread switches (or 'none'). Award 2 points for (iii) correctly listing voluntary switches (thread exit, yield, block/sleep). Partial credit allowed per item."
}
```

c.  (4 marks) cvwait
List, in order, the four steps of cv_wait. Do not list any of the KASSERTs.

```json
{
  "problem_id": "2c",
  "points": 4,
  "type": "Freeform",
  "tags": ["cv-wait","synchronization"],
  "answer": "1) wchan_lock(cv->wchan) 2) lock_release(lk) 3) wchan_sleep(cv->wchan) 4) lock_acquire(lk)",
  "llm_judge_instructions": "Award 1 point for each correct step in the correct order (1 point each for steps 1 through 4). If steps are present but order is wrong, award partial credit up to 2 points."
}
```

---

## Question 3 [14 point(s)]

For the following questions a single sentence answer will suffice.

a.  (1 mark)
Under what case (or cases) does disabling interrupts enforce mutual exclusion?

```json
{
  "problem_id": "3a",
  "points": 1,
  "type": "Freeform",
  "tags": ["mutex","interrupts"],
  "answer": "Disabling interrupts enforces mutual exclusion on a uniprocessor (single-core) system.",
  "llm_judge_instructions": "Award 1 point if the student states that disabling interrupts enforces mutual exclusion on a single-core (single-processor) system; 0 otherwise."
}
```

b.  (1 mark)
Give one disadvantage of a scheduling quantum that is too short (i.e., 1ms or less).

```json
{
  "problem_id": "3b",
  "points": 1,
  "type": "Freeform",
  "tags": ["scheduling"],
  "answer": "Excessive context switching leading to wasted CPU time and reduced forward progress per thread.",
  "llm_judge_instructions": "Award 1 point for stating that too-short quanta cause excessive preemption/context-switch overhead and wasted CPU cycles or reduced progress."
}
```

c.  (1 mark)
Give one disadvantage of a scheduling quantum that is too long (i.e., 1s or more).

```json
{
  "problem_id": "3c",
  "points": 1,
  "type": "Freeform",
  "tags": ["scheduling"],
  "answer": "Reduced responsiveness and poor interactivity because threads wait too long to be scheduled.",
  "llm_judge_instructions": "Award 1 point for noting decreased responsiveness or perceived lack of concurrency due to long quanta."
}
```

d.  (1 mark)
What do exceptions and interrupts have in common?

```json
{
  "problem_id": "3d",
  "points": 1,
  "type": "Freeform",
  "tags": ["interrupts","exceptions"],
  "answer": "Both transfer control to the kernel (cause control flow to switch to kernel-mode handler).",
  "llm_judge_instructions": "Award 1 point for identifying that both exceptions and interrupts transfer control to the kernel or invoke kernel handlers."
}
```

e.  (1 mark)
What would be a scenario (if any) where a kernel stack would have a trapframe pushed and popped without a switchframe also being pushed and popped?

```json
{
  "problem_id": "3e",
  "points": 1,
  "type": "Freeform",
  "tags": ["kern-stack","trapframe"],
  "answer": "An interrupt that is handled entirely within the current thread (e.g., device interrupt or timer interrupt) where no thread switch occurs.",
  "llm_judge_instructions": "Award 1 point for describing that an interrupt/exception handled without a context switch (e.g., a short device or timer interrupt) can push/pop a trapframe without switchframe activity."
}
```

f.  (1 mark)
What would be a scenario (if any) where a kernel stack would have a switchframe pushed and popped without a trapframe also being pushed and popped?

```json
{
  "problem_id": "3f",
  "points": 1,
  "type": "Freeform",
  "tags": ["kern-stack","switchframe"],
  "answer": "A voluntary context switch inside the kernel (e.g., thread yield while already in kernel mode) where no new trapframe is created.",
  "llm_judge_instructions": "Award 1 point for indicating that a kernel-initiated context switch (e.g., thread yield or thread switch in kernel code) can push/pop a switchframe without a trapframe."
}
```

g.  (1 mark)
Why can’t you have a pid of 0 in os/161?

```json
{
  "problem_id": "3g",
  "points": 1,
  "type": "Freeform",
  "tags": ["os161","pids"],
  "answer": "Because fork returns 0 to the child, so 0 is used as a special return value and is not a valid pid.",
  "llm_judge_instructions": "Award 1 point for explaining that pid 0 is invalid because fork() uses 0 as the child return value; 0 otherwise."
}
```

h.  (2 marks)
A programmer is writing a program that requires two major (but independent) tasks to be performed and is trying to decide between using fork (assigning one task to parent and one to child) or using thread fork (one task per thread).
i) What would be one advantage of using fork?
ii) What would be one advantage of using thread fork?

```json
{
  "problem_id": "3h",
  "points": 2,
  "type": "Freeform",
  "tags": ["processes","threads"],
  "answer": "i) fork: process isolation so a crash in one does not affect the other. ii) thread fork: lower memory overhead and easier shared-memory communication.",
  "llm_judge_instructions": "Award 1 point for (i) mentioning process isolation or fault containment. Award 1 point for (ii) mentioning lower memory overhead or easier inter-thread communication/shared state. Partial credit allowed if answer implies these benefits."
}
```

i.  (3 total marks)
Draw the user and kernel stacks for a process that is executing sys_waitpid. Show the top of the stack at the bottom of the diagram.

```json
{
  "problem_id": "3i",
  "points": 3,
  "type": "Freeform",
  "tags": ["kern-stack","waitpid"],
  "answer": "User stack: application frames including waitpid call. Kernel stack (top at bottom): trapframe -> mipstrap/syscall entry -> sys_waitpid kernel frames.",
  "llm_judge_instructions": "Award up to 3 points: 1 point for showing user frames with waitpid, 1 point for including a trapframe on the kernel stack, and 1 point for showing syscall entry and sys_waitpid kernel frames in the correct order (top at bottom)."
}
```

j.  (2 total marks)
Explain how the following kernel stack could come to be: two trapframes consecutively on the kernel stack.

```json
{
  "problem_id": "3j",
  "points": 2,
  "type": "Freeform",
  "tags": ["kern-stack","exception"],
  "answer": "A nested interrupt or exception occurred where an interrupt was enabled (or a second interrupt arrived) while handling the first, resulting in a second trapframe being pushed.",
  "llm_judge_instructions": "Award 2 points for explaining nested interrupts/exceptions (e.g., a handler enabled interrupts or another device interrupt occurred) leading to multiple trapframes; 1 point for partially correct scenarios."
}
```

---

## Question 4 [10 point(s)]

The following pseudocode makes use of a semaphore. Replace the semaphore-based implementation with a condition-variable-based implementation that performs the same task. You may only add up to three additional variables. Your cv may not be used with a loop.

Original semaphore-based code (for context):
Semaphore barrier; // initialized to 0
int CS350( void * v, long n )
{
  WriteMidterm();
  V(barrier);
}
int main()
{
  for ( int i = 0; i < NUMTHREADS; i++ )
    thread_fork("student", NULL, CS350, NULL, i );
  for ( int i = 0; i < NUMTHREADS; i++ )
    P( barrier );
  MarkMidterms();
}

Provide a condition-variable-based replacement implementation.

```json
{
  "problem_id": "4",
  "points": 10,
  "type": "Freeform",
  "tags": ["conditional-variable","barrier","synchronization"],
  "answer": "Use: int count = 0; lock_t countLock; cv_t barrier_cv; Each student thread acquires countLock, increments count, if count == NUMTHREADS then cv_signal(barrier_cv) (or cv_broadcast depending on design), releases countLock. Main acquires countLock, if count != NUMTHREADS then cv_wait(countLock, barrier_cv), then releases countLock and calls MarkMidterms().",
  "llm_judge_instructions": "Allocate 10 points as follows: 3 points for declaring acceptable additional variables (1 pt each up to 3: count, countLock, barrier_cv). 3 points for student thread behavior: 1 pt for acquiring lock before incrementing, 1 pt for incrementing count, 1 pt for signaling when count==NUMTHREADS. 4 points for main-thread behavior: 2 pts for acquiring lock and waiting on cv correctly (cv_wait with lock held), 1 pt for checking count condition correctly, 1 pt for releasing lock and proceeding to MarkMidterms. Partial credit awarded proportionally."
}
```

---

## Question 5 [10 point(s)]

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
  lk->owner = cur_thread;
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
  "problem_id": "5",
  "points": 10,
  "type": "Freeform",
  "tags": ["locking","mutex","kernel"],
  "answer": "Corrected implementation summary: Do not release lk->sem before setting owner to NULL in release; use P(lk->sem) to enter critical section of release, set owner to NULL, wake one waiter, then V(lk->sem). Ensure acquire asserts not already owner and uses sem to protect owner access.",
  "llm_judge_instructions": "Award up to 10 points distributed as follows: 2 points for correctly identifying that original code does not guarantee mutual exclusion (explain why). 4 points for a corrected lock_acquire implementation (protect owner with sem, proper ordering, and ownership assignment). 4 points for a corrected lock_release implementation (ensure P on sem before modifying owner, call wchan_wakeone, then V on sem) and fixing other issues such as appropriate KASSERTs. Partial credit awarded for partial corrections and correct reasoning."
}
```

---

## Question 6 [8 point(s)]

A system uses segmented address space for its implementation of virtual memory. Suppose a process initially uses 48KB of memory for its heap. The process then requests 16 KB more space. Assume sbrk(16*1024) will request that the heap’s space be increased by 16 KB by finding a new location in RAM for the heap segment. If successful it returns the new address, otherwise it returns NULL.

In roughly 4–6 steps, describe the process that would be required to increase the process’s address space.

```json
{
  "problem_id": "6",
  "points": 8,
  "type": "Freeform",
  "tags": ["vm","sbrk","memory-management"],
  "answer": "Typical steps: (1) Check if sufficient physical memory/VM resources are available; if not, return ENOMEM. (2) Allocate a new heap segment region of the larger size (e.g., 48KB+16KB). (3) Copy the contents of the old heap to the new region. (4) Update the process's segment relocation and limit registers in the kernel. (5) Update MMU page tables / mappings to reflect the new physical addresses. (6) Free the old heap region and return the new heap base.",
  "llm_judge_instructions": "Award up to 8 points: 1 point for checking space and returning ENOMEM if needed; 2 points for allocating the new region correctly; 2 points for copying existing heap contents safely; 2 points for updating kernel process segment registers and MMU mappings; 1 point for deallocating the old heap region and returning the new address. Partial credit for partial or out-of-order but reasonable steps."
}
```

---

## Question 7 [8 point(s)]

A system uses 24-bit virtual addresses, 24-bit physical addresses and memory segmentation. There are four segments and two bits are used for the segment number. The relocation and limit for each of the segments are as follows.

Segment Number | Limit Register | Relocation Register
0x0 | 0x2 0000 | 0x40 0000
0x1 | 0xC 0000 | 0x70 0000
0x2 | 0x9 0000 | 0x50 0000
0x3 | 0xA 0000 | 0x60 0000

Translate the following addresses from virtual to physical. Clearly indicate what segment each address belongs to.

a. (2 marks) 0x01D0D4
b. (2 marks) 0x22CA10
c. (2 marks) 0x3347B8
d. (2 marks) 0x1CF008

```json
{
  "problem_id": "7",
  "points": 8,
  "type": "Freeform",
  "tags": ["vm","segmentation","address-translation"],
  "answer": "a) Segment 0x0, offset 0x1D0D4 -> physical = relocation 0x400000 + 0x1D0D4 = 0x41D0D4. b) Segment 0x2, offset 0x2CA10 -> check limit (0x9 0000 = 0x90000); if offset 0x2CA10 < limit then physical = relocation 0x500000 + 0x2CA10 = 0x52CA10, else segmentation violation. c) Segment 0x3, offset 0x347B8 -> check limit (0xA0000 = 0xA0000); if offset < limit then physical = relocation 0x600000 + 0x347B8 = 0x6347B8, else segmentation violation. d) Segment 0x1, offset 0xCF008 -> check limit (0xC0000 = 0xC0000); if offset 0xCF008 >= 0xC0000 then segmentation violation else physical = relocation 0x700000 + offset.",
  "llm_judge_instructions": "Award 2 points per subpart: 1 point for correct segment extraction, 1 point for correct translation or correct identification of segmentation violation based on the segment limit. If offset exceeds the limit, credit for stating 'segmentation violation'. Partial credit allowed per subpart."
}
```

---

## Question 8 [8 point(s)]

Ideally any scheme to enforce mutual exclusion should satisfy the following constraints.
i. Only one thread is allowed in a critical section at a time.
ii. No assumptions can be made about the order different threads will access the critical section.
iii. A thread that is outside the critical section cannot prevent another thread from entering the critical section.
iv. At least one thread should be making progress.
v. There should be a bound on the time a thread must wait.

For each of four cases listed below there are only two threads, T1 and T2. Rather than use locks, the threads use the code below to provide mutual exclusion to a critical region. Each thread will be trying to access the critical region multiple times.

a. (2 marks)
T1 and T2 both execute the same function.

#define CLOSED 0
#define OPEN   1
volatile int Lock = OPEN; // global variable
AccessCriticalRegion() {
  while (Lock == CLOSED) {;} // busy wait
  Lock = CLOSED;
  CriticalSection();
  Lock = OPEN;
}
Does this scheme meet all the requirements? If not, which requirement is not satisfied? Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "8a",
  "points": 2,
  "type": "Freeform",
  "tags": ["synchronization","mutual-exclusion"],
  "answer": "This does not guarantee mutual exclusion (violates (i)). A race exists between the test and set: both threads may observe Lock==OPEN and then both execute Lock = CLOSED, allowing both into the critical section.",
  "llm_judge_instructions": "Award 2 points for identifying that requirement (i) is violated and providing a scenario describing the race between reading Lock==OPEN and setting Lock=CLOSED leading to both threads entering. Award 1 point for correctly naming the violated requirement without a clear scenario."
}
```

b. (2 marks)
Here T1 and T2 use different functions to access the critical region.

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
Does this scheme meet all the requirements? If not, which requirement is not satisfied? Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "8b",
  "points": 2,
  "type": "Freeform",
  "tags": ["synchronization","mutual-exclusion"],
  "answer": "This can violate (iii): a thread outside the critical section can block the other. For example, if Last==1 but T2 has not entered the critical section, T1 may be prevented from entering while Last remains 1.",
  "llm_judge_instructions": "Award 2 points for identifying that requirement (iii) is violated and giving a clear scenario showing how a thread outside the critical section can prevent the other thread from entering. Award 1 point for a partially correct explanation."
}
```

c. (2 marks)
Here T1 and T2 use different functions to access the critical region.

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
Does this scheme meet all the requirements? If not, which requirement is not satisfied? Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "8c",
  "points": 2,
  "type": "Freeform",
  "tags": ["synchronization","mutual-exclusion"],
  "answer": "This can deadlock (violates (iv) progress). If both set their flag (T1=WANT_IN and T2=WANT_IN) concurrently, each will spin forever waiting for the other to clear its flag.",
  "llm_judge_instructions": "Award 2 points for identifying that the scheme can deadlock (progress violation (iv)) and describing the scenario where both threads set WANT_IN and then spin forever. Award 1 point for partial explanation."
}
```

d. (2 marks)
Here T1 and T2 use different functions to access the critical region. (This is Dekker-like with Last variable)

Does this scheme meet all the requirements? If not, which requirement is not satisfied? Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "8d",
  "points": 2,
  "type": "Freeform",
  "tags": ["synchronization","mutual-exclusion"],
  "answer": "This scheme is designed to satisfy mutual exclusion and progress (it is a Dekker-like algorithm using Last to break ties), so it meets the requirements in typical models without weak memory reordering.",
  "llm_judge_instructions": "Award 2 points if the student states that the scheme works and provides a brief justification that Last resolves conflicts and prevents concurrent entry. If the student objects due to memory ordering concerns, award 1 point for noting the issue with appropriate reasoning."
}
```