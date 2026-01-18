# CS350 Winter 2019 Midterm

```json
{
  "exam_id": "cs350_winter_2019_midterm",
  "test_paper_name": "CS350 Winter 2019 Midterm",
  "course": "CS350",
  "institution": "University of Waterloo",
  "year": 2019,
  "score_total": 60,
  "num_questions": 23
}
```

---

## Question 1a [2 point(s)]

Which is typically faster and why:

- Printing the numbers from 1 to 1000000, one number at a time.
- Creating a string with the numbers from 1 to 1000000 and printing that string.

```json
{
  "problem_id": "1a",
  "points": 2,
  "type": "Freeform",
  "tags": ["efficiency"],
  "answer": "B is faster.",
  "llm_judge_instructions": "Award 2 points for stating that option B is faster and giving the justification that printing numbers one by one causes many system calls (e.g., ~1,000,000) while constructing and printing a single string uses far fewer system calls (e.g., one). Award 1 point if B is stated but the justification is incomplete or only mentions reduced overhead without referencing system calls or buffering. Award 0 points otherwise."
}
```

---

## Question 1b [2 point(s)]

Can you still have concurrency if you have a single processor with a single core and the degree of threading is one (i.e. P=1, C=1, M=1)?

```json
{
  "problem_id": "1b",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency"],
  "answer": "Yes",
  "llm_judge_instructions": "Award 2 points for answering Yes and providing justification that preemption or timesharing allows the processor to rapidly switch between threads/processes so that multiple activities make progress over time. Award 0 points otherwise."
}
```

---

## Question 1c [2 point(s)]

Can a lock be used anywhere a binary semaphore is used?

```json
{
  "problem_id": "1c",
  "points": 2,
  "type": "Freeform",
  "tags": ["synchronization"],
  "answer": "No.",
  "llm_judge_instructions": "Award 2 points for stating No and providing a brief justification that lock semantics require the same thread to both acquire and release the lock (ownership), whereas a binary semaphore allows P and V operations by different threads and does not enforce ownership. Award 0 points otherwise."
}
```

---

## Question 2a [2 point(s)]

List two possible advantages of concurrency.

```json
{
  "problem_id": "2a",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency"],
  "answer": "Improved CPU utilization; Improved performance.",
  "llm_judge_instructions": "Award 2 points for listing two distinct, correct advantages (for example: improved CPU utilization, higher throughput, better responsiveness). Award 1 point if only one correct advantage is given. Award 0 points otherwise."
}
```

---

## Question 2b [4 point(s)]

Context Switching. There are a number of ways that a context switch can occur.
i Which ones are prevented when interrupts are turned off.
ii Which ones are prevented when each process only has a single thread of execution.
iii Which ones are not prevented by either of the two previous conditions.

```json
{
  "problem_id": "2b",
  "points": 4,
  "type": "Freeform",
  "tags": ["context-switching"],
  "answer": "i: preemption; ii: none; iii: thread-exit, thread-yield, thread-block or sleep",
  "llm_judge_instructions": "Award 1 point for correctly identifying which context switches are prevented when interrupts are turned off (part i). Award 1 point for correctly identifying which context switches are prevented when each process has only a single thread (part ii). Award 2 points for correctly listing the context switches that are not prevented by either condition (part iii). For part iii, if the answer is partially correct, award 1 point."
}
```

---

## Question 2c [4 point(s)]

cvwait
List, in order, the four steps of cv wait. Do not list any of the KASSERTs.
1.
2.
3.
4.

```json
{
  "problem_id": "2c",
  "points": 4,
  "type": "Freeform",
  "tags": ["cvwait"],
  "answer": "1. wchanlock(cv->wchan); 2. lock_release(lk); 3. wchansleep(cv->wchan); 4. lock_acquire(lk)",
  "llm_judge_instructions": "Award 1 point for each correct step listed in the correct order (1 point each for steps 1–4). Award 0 points for an incorrect or missing step. Total = 4 points."
}
```

---

## Question 3 [10 point(s)]

The following pseudocode makes use of a semaphore. Replace the semaphore based implementation with a condition variable based implementation that performs the same task. You may only add up to three additional variables. Your cv may not be used with a loop.

Semaphore barrier; // initialized to 0
int CS350( void * v, long n )
{
WriteMidterm()
V(barrier);
}
int main()
{
for ( int i = 0; i <  NUMTHREADS; i ++ )
thread_fork(‘‘student’’, null, CS350, null, i );
for ( int i = 0; i < NUMTHREADS; i ++ )
P( barrier );
MarkMidterms()
}
int count = 0; [1 mark]
lock countLock; [1 mark]
cv barrier; [1 mark]
int KernelFunction( void * v, long n )
{
...
acquire( countLock ); [1 mark]
count ++; [1 mark]
if ( count == NUMTHREADS ) cv_signal( countLock, barrier ); [1 mark]
release( countLock ); [1 mark]
}
int main()
{
for ( int i = 0; i <  NUMTHREADS; i ++ )
thread_fork( \", null, KernelFunction, null, i );
acquire( countLock ); [1 mark]
if ( count != NUMTHREADS ) cv_wait( countLock, barrier ); [1 mark]
release( countLock ); [1 mark]
}

```json
{
  "problem_id": "3",
  "points": 10,
  "type": "Freeform",
  "tags": ["condition-variables"],
  "answer": "Converted to a CV-based implementation that uses up to 3 extra variables, does not use cv_wait in a loop, and preserves barrier semantics.",
  "llm_judge_instructions": "Award 1 point each for the following items (total 10): 1) initialize count to 0 (1 pt), 2) create/initialize the countLock (1 pt), 3) create/initialize the barrier CV (1 pt), 4) acquire countLock in each thread before modifying count (1 pt), 5) increment count under the lock (1 pt), 6) signal the CV when count == NUMTHREADS (1 pt), 7) release countLock after updating count (1 pt), 8) in main, acquire countLock before checking count (1 pt), 9) call cv_wait(countLock, barrier) in main if count != NUMTHREADS (1 pt), 10) release countLock in main after wait/check (1 pt). Deduct points for incorrect use of loops around cv_wait or for using more than three additional variables."
}
```

---

## Question 4a [2 point(s)]

(a) If this lock was used to protect a critical section, would it guarantee mutual exclusion?

```json
{
  "problem_id": "4a",
  "points": 2,
  "type": "Freeform",
  "tags": ["locks"],
  "answer": "No.",
  "llm_judge_instructions": "Award 2 points for stating No and providing a brief reason explaining why mutual exclusion would not be guaranteed by the given lock implementation. Award 0 points otherwise."
}
```

---

## Question 4b [4 point(s)]

(b) If you answered yes to (a), why? If you answered no to (a), correct the code (you may edit the code in-place).

```json
{
  "problem_id": "4b",
  "points": 4,
  "type": "Freeform",
  "tags": ["locks"],
  "answer": "Corrected code snippet with proper ownership checks and semaphore handling.",
  "llm_judge_instructions": "Award points as follows (total 4): 2 points for identifying the primary correctness issue (e.g., missing ownership checks or incorrect use of semaphore primitives), 1 point for showing corrected semaphore/lock usage (e.g., proper acquire/release semantics), and 1 point for any additional necessary fixes (e.g., removing incorrect assertions or restoring owner tracking). Partial credit allowed based on these criteria."
}
```

---

## Question 4c [4 point(s)]

(c) If there are any other issues with the lock not related to mutual exclusion, correct them. Otherwise, indicate the implementation is correct.

```json
{
  "problem_id": "4c",
  "points": 4,
  "type": "Freeform",
  "tags": ["locks"],
  "answer": "The implementation is correct.",
  "llm_judge_instructions": "Award 4 points for correctly identifying that the implementation has no other issues and providing a concise justification. Award 2 points for a partially correct identification or partial justification. Award 0 points if incorrect."
}
```

---

## Question 5 [8 point(s)]

A system uses segmented address space for its implementation of virtual memory. Suppose a process initially uses 48KB of memory for its heap. The process then runs low on heap space and requests 16 KB more space. Assume you have access to a procedure sbrk and that sbrk(16*1024) will request that the heap’s space be increased by 16 KB by finding a new location in RAM for the heap segment. If successful it returns the new address, otherwise it return NULL.
In roughly 4–6 steps, describe the process that would be required to increase the process’s address space.

- Check if there is enough space to accommodate the new, larger heap (1 mark) or return ENOMEM (1 mark).
- Allocate the new heap (1 mark)
- Copy the contents of the old heap to the new one.  (2 marks)
- Update the proc’s relocation and limit values for the heap in the kernel (1 mark) and on the MMU (1 mark).
- Delete the old heap (1 mark)

```json
{
  "problem_id": "5",
  "points": 8,
  "type": "Freeform",
  "tags": ["virtual-memory"],
  "answer": "Steps to increase heap: (1) Check available space; if insufficient, return ENOMEM. (2) Allocate new heap region. (3) Copy old heap content to the new region. (4) Update process relocation and limit values for the heap in the kernel. (5) Update the MMU mapping for the heap. (6) Delete the old heap region and return the new address.",
  "llm_judge_instructions": "Award points as follows (total 8): 1 point for checking available space and handling the ENOMEM case, 1 point for allocating the new heap region, 2 points for correctly copying the old heap contents to the new region, 1 point for updating the kernel's process relocation/limit metadata, 1 point for updating the MMU/page table mappings, 1 point for deleting/freeing the old heap region, and 1 point for returning/updating the process's heap pointer (sbrk return). Partial credit allowed per item."
}
```

---

## Question 6a [2 point(s)]

Translate the following addresses from virtual to physical. Clearly indicate what segment each address belongs to.
a. 0x01 D0D4

```json
{
  "problem_id": "6a",
  "points": 2,
  "type": "Freeform",
  "tags": ["segmentation"],
  "answer": "Segment Number: (your answer) ; Address Translation: (your translation) ",
  "llm_judge_instructions": "Award 2 points for correctly identifying the segment and providing the correct physical address translation. Award 0 points otherwise."
}
```

---

## Question 6b [2 point(s)]

b. 0x22 CA10

```json
{
  "problem_id": "6b",
  "points": 2,
  "type": "Freeform",
  "tags": ["segmentation"],
  "answer": "Segment Number: (your answer) ; Address Translation: (your translation) ",
  "llm_judge_instructions": "Award 2 points for correctly identifying the segment and providing the correct physical address translation. Award 0 points otherwise."
}
```

---

## Question 6c [2 point(s)]

c. 0x33 47B8

```json
{
  "problem_id": "6c",
  "points": 2,
  "type": "Freeform",
  "tags": ["segmentation"],
  "answer": "Segment Number: (your answer) ; Address Translation: (your translation) ",
  "llm_judge_instructions": "Award 2 points for correctly identifying the segment and providing the correct physical address translation. Award 0 points otherwise."
}
```

---

## Question 6d [2 point(s)]

d. 0x1C F008

```json
{
  "problem_id": "6d",
  "points": 2,
  "type": "Freeform",
  "tags": ["segmentation"],
  "answer": "Segment Number: (your answer) ; Address Translation: (your translation) ",
  "llm_judge_instructions": "Award 2 points for correctly identifying the segment and providing the correct physical address translation. Award 0 points otherwise."
}
```

---

## Question 7a [2 point(s)]

a. Here T1 and T2 both execute the same function.
#define CLOSED 0
#define OPEN   1
volatile int Lock = OPEN; // global variable
AccessCriticalRegion() {
1    while (Lock == CLOSED) {;} // busy wait
2    Lock = CLOSED;
3    CriticalSection();
4    Lock = OPEN;
}
Does this scheme meet all the requirements? If not, which requirement is not satisfied?  Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "7a",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "No. The scheme violates mutual exclusion because between the check of Lock in the while and the assignment Lock = CLOSED another thread could run and also observe Lock as OPEN, leading both to enter the critical section.",
  "llm_judge_instructions": "Award 2 points for identifying that mutual exclusion is not guaranteed and providing a scenario where a context switch occurs after the check but before setting Lock to CLOSED, allowing both threads to enter. Award 1 point for partially correct reasoning. Award 0 points otherwise."
}
```

---

## Question 7b [2 point(s)]

b. Here T1 and T2 use different functions to access the critical region.
volatile int Last = 2; // global variable
// Code for T1
T1AccessCriticalRegion() {
1   while (Last == 1){;}
2   CriticalSection();
3   Last = 1;
}
// Code for T2
T2AccessCriticalRegion() {
1   while (Last == 2){;}
2   CriticalSection();
3   Last = 2;
}
Does this scheme meet all the requirements? If not, which requirement is not satisfied?  Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "7b",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "This scheme may violate progress/fairness requirements (e.g., can lead to starvation) depending on timing; it serializes access but can prevent a thread from entering under some schedules.",
  "llm_judge_instructions": "Award 2 points for identifying which requirement is not satisfied (for example, progress or absence of starvation) and providing a concrete scenario demonstrating the violation. Award 1 point for partial explanation. Award 0 points otherwise."
}
```

---

## Question 7c [2 point(s)]

c. Here T1 and T2 use different functions to access the critical region.
#define WANT_IN 1
volatile int T1 = ! WANT_IN; // global variables
volatile int T2 = ! WANT_IN;
// Code for T1
T1AccessCriticalRegion() {
1   T1 = WANT_IN;
2   while (T2 == WANT_IN){;}
3   CriticalSection();
4   T1 = ! WANT_IN;
}
// Code for T2
T2AccessCriticalRegion() {
1   T2 = WANT_IN;
2   while (T1 == WANT_IN){;}
3   CriticalSection();
4   T2 = ! WANT_IN;
}
Does this scheme meet all the requirements? If not, which requirement is not satisfied? Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "7c",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "This scheme can deadlock (violate progress) if both threads set their WANT_IN flag and then spin waiting for the other to clear it, causing no one to enter the critical section.",
  "llm_judge_instructions": "Award 2 points for identifying the potential for deadlock and describing the scenario where both threads set WANT_IN and then busy-wait on the other's flag. Award 1 point for a partial explanation. Award 0 points otherwise."
}
```

---

## Question 7d [2 point(s)]

d. Here T1 and T2 use different functions to access the critical region.
#define WANT_IN 1
volatile int T1 = ! WANT_IN; // global variables
volatile int T2 = ! WANT_IN;
volatile int Last = 1;
// Code for T1
T1AccessCriticalRegion() {
1   while (1) {
2      T1 = WANT_IN;
3      if (T2 == !WANT_IN) {
4         break;
5      }
6     if (Last == 1) {
7        T1 = !WANT_IN;
8        while (Last == 1){;}
9     }
10   }
11  CriticalSection();
12  Last = 1;
13  T1 = ! WANT_IN;
}
// Code for T2
T2AccessCriticalRegion() {
1  while (1) {
2    T2 = WANT_IN;
3    if (T1 == !WANT_IN) {
4      break;
5    }
6    if (Last == 2) {
7      T2 = !WANT_IN;
8      while (Last == 2){;}
9    }
10  }
11  CriticalSection();
12  Last = 2;
13  T2 = ! WANT_IN;
}
Does this scheme meet all the requirements? If not, which requirement is not satisfied? Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "7d",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "This is an implementation of Peterson-like algorithm with the Last variable to break ties; it satisfies mutual exclusion and progress for two threads.",
  "llm_judge_instructions": "Award 2 points for stating that the scheme works (mutual exclusion and progress) and providing a concise justification why the Last variable prevents deadlock and enforces mutual exclusion. Award 1 point for partial justification. Award 0 points otherwise."
}
```

---

## Question 8a [2 point(s)]

a. Here T1 and T2 both execute the same function.
#define CLOSED 0
#define OPEN   1
volatile int Lock = OPEN; // global variable
AccessCriticalRegion() {
1    while (Lock == CLOSED) {;} // busy wait
2    Lock = CLOSED;
3    CriticalSection();
4    Lock = OPEN;
}
Does this scheme meet all the requirements? If not, which requirement is not satisfied?  Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "8a",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "No. The scheme violates mutual exclusion because two threads can both see Lock as OPEN and both proceed to set it to CLOSED, entering the critical section concurrently.",
  "llm_judge_instructions": "Award 2 points for identifying the violated requirement (mutual exclusion) and giving a scenario where a context switch occurs after the while check but before setting Lock to CLOSED. Award 1 point for partial explanation. Award 0 points otherwise."
}
```

---

## Question 8b [2 point(s)]

b. Here T1 and T2 use different functions to access the critical region.
volatile int Last = 2; // global variable
// Code for T1
T1AccessCriticalRegion() {
1   while (Last == 1){;}
2   CriticalSection();
3   Last = 1;
}
// Code for T2
T2AccessCriticalRegion() {
1   while (Last == 2){;}
2   CriticalSection();
3   Last = 2;
}
Does this scheme meet all the requirements? If not, which requirement is not satisfied?  Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "8b",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "This scheme enforces strict alternation, which can violate progress/fairness (e.g., a thread that is not ready forces the other to wait). It may cause unnecessary blocking and reduce concurrency.",
  "llm_judge_instructions": "Award 2 points for identifying that the scheme enforces strict alternation and explaining how that can violate requirements (such as progress or responsiveness) with a concrete scenario. Award 1 point for partial reasoning. Award 0 points otherwise."
}
```

---

## Question 8c [2 point(s)]

c. Here T1 and T2 use different functions to access the critical region.
#define WANT_IN 1
volatile int T1 = ! WANT_IN; // global variables
volatile int T2 = ! WANT_IN;
// Code for T1
T1AccessCriticalRegion() {
1   T1 = WANT_IN;
2   while (T2 == WANT_IN){;}
3   CriticalSection();
4   T1 = ! WANT_IN;
}
// Code for T2
T2AccessCriticalRegion() {
1   T2 = WANT_IN;
2   while (T1 == WANT_IN){;}
3   CriticalSection();
4   T2 = ! WANT_IN;
}
Does this scheme meet all the requirements? If not, which requirement is not satisfied? Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "8c",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "This scheme can deadlock: if both threads set their WANT_IN flag simultaneously, both will spin waiting for the other, preventing progress.",
  "llm_judge_instructions": "Award 2 points for identifying the potential deadlock and describing the simultaneous WANT_IN scenario. Award 1 point for partial explanation. Award 0 points otherwise."
}
```

---

## Question 8d [2 point(s)]

d. Here T1 and T2 use different functions to access the critical region.
#define WANT_IN 1
volatile int T1 = ! WANT_IN; // global variables
volatile int T2 = ! WANT_IN;
volatile int Last = 1;
// Code for T1
T1AccessCriticalRegion() {
1   while (1) {
2      T1 = WANT_IN;
3      if (T2 == !WANT_IN) {
4         break;
5      }
6     if (Last == 1) {
7        T1 = !WANT_IN;
8        while (Last == 1){;}
9     }
10   }
11  CriticalSection();
12  Last = 1;
13  T1 = !WANT_IN;
}
// Code for T2
T2AccessCriticalRegion() {
1  while (1) {
2    T2 = WANT_IN;
3    if (T1 == !WANT_IN) {
4      break;
5    }
6    if (Last == 2) {
7      T2 = !WANT_IN;
8      while (Last == 2){;}
9    }
10  }
11  CriticalSection();
12  Last = 2;
13  T2 = !WANT_IN;
}
Does this scheme meet all the requirements? If not, which requirement is not satisfied? Give a scenario where that requirement would not be satisfied.

```json
{
  "problem_id": "8d",
  "points": 2,
  "type": "Freeform",
  "tags": ["mutual-exclusion"],
  "answer": "It works.",
  "llm_judge_instructions": "Award 2 points for stating that the scheme enforces mutual exclusion and progress for the two-thread case and providing a concise justification (e.g., explaining how Last breaks ties). Award 1 point for partial justification. Award 0 points otherwise."
}
```