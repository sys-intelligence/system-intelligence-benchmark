# CS530 Fall 2015 Midterm

```json
{
  "exam_id": "cs530_fall_2015_midterm",
  "test_paper_name": "CS530 Fall 2015 Midterm",
  "course": "CS 530",
  "institution": "University of Waterloo",
  "year": 2015,
  "score_total": 70,
  "num_questions": 19
}
```

---

## Question 1 [12 point(s)]

1. (12 total marks)

Consider the following concurrent program fragment that uses semaphores:

Global variables and initialization:
struct semaphore *sa;
struct semaphore *sb;
struct semaphore *sc;
sa = semcreate("A",1);
sb = semcreate("B",1);
sc = semcreate("C",0);

void func1(){
  P(sa);
  funcA();
  V(sa);
  P(sc);
}

void func2(){
  P(sb);
  funcB();
  V(sb);
  V(sc);
}

Suppose the initialization code is executed once by the initial thread, which then creates many new threads, some of which run func1 and some of which run func2. func1 and func2 call funcA and funcB respectively (not shown).

Re-implement func1 and func2 without using semaphores. Instead, use locks and condition variables for synchronization. Your re-implemented functions must have the same behavior as the original functions shown above. You may create as many locks, condition variables, and other global variables as you need. Be sure to show global variable declarations and initialization, as well as the implementations of func1 and func2.

```json
{
  "problem_id": "1",
  "points": 12,
  "type": "Freeform",
  "tags": ["synchronization", "semaphores", "locks", "condition-variables"],
  "answer": "The correct answer goes here (from solutions file)",
  "llm_judge_instructions": "Award up to 12 points as follows: 4 points for correct and complete global variable declarations and initialization (locks, condition variables, and any counters used); 4 points for a correct implementation of func1 that ensures mutual exclusion equivalent to P(sa)/V(sa) around funcA and that waits appropriately for the condition represented by sc; 4 points for a correct implementation of func2 that ensures mutual exclusion equivalent to P(sb)/V(sb), updates shared state consistently, and signals/wakes waiting threads to implement the semantics of V(sc). Deduct points for solutions that can deadlock, lose wakeups, or otherwise fail to preserve the original semaphore behavior. Do not award credit for solutions that still use semaphores."
}
```

---

## Question 2a [2 point(s)]

2a. (2 marks)

What is the maximum number of entries in a page table in this system?

```json
{
  "problem_id": "2a",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "16",
  "llm_judge_instructions": "Award 2 points for correctly answering 16. Award 0 points otherwise."
}
```

---

## Question 2b [4 point(s)]

2b. (4 marks)

A process P1 has the following page table. Frame numbers are given in hexadecimal notation (each hexadecimal digit represents 4 bits).

Page Number  Frame Number
00           x1010
10           x2034
20           x43AC
30           x1100
40           xAC11
50           x8000

For each of the following physical addresses, indicate the virtual address to which it maps. If the physical address is not part of the physical memory assigned to P1, write NO TRANSLATION instead. Use hexadecimal notation for the virtual addresses.

- 0x1100A0
- 0xAC1100
- 0xBA3424
- 0x43ACA0
- 0x3A0
- 0x400
- NO TRANSLATION
- 0x2A0

```json
{
  "problem_id": "2b",
  "points": 4,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "The correct virtual addresses corresponding to the given physical addresses (based on the provided page table).",
  "llm_judge_instructions": "Award points up to 4 using the following integer rubric: 4 points if all mappings are correct; 3 points if 6–7 mappings are correct; 2 points if 4–5 mappings are correct; 1 point if 1–3 mappings are correct; 0 points if none are correct. Do not award fractional points."
}
```

---

## Question 2c [2 point(s)]

2c. (2 marks)

Due to a bug in the OS/161 as copy function, the following is the page table of P1’s child process immediately after it returns from fork. Mark the entries in the page table that you are certain to be incorrect.

Page Number  Frame Number
00           x2453
10           x1010
20           xEA35
30           x3100
40           x2034
50           x9012

```json
{
  "problem_id": "2c",
  "points": 2,
  "type": "Freeform",
  "tags": ["os161", "fork"],
  "answer": "10x1010, 40x2034",
  "llm_judge_instructions": "Award full credit (2 points) if the two entries that must be incorrect (the ones that violate expected copy-on-fork behavior in context) are identified. Award 0 points otherwise."
}
```

---

## Question 2d [2 point(s)]

2d. (2 marks)

Name one advantage and one disadvantage of having a virtual address space that is smaller than the physical address space.

```json
{
  "problem_id": "2d",
  "points": 2,
  "type": "Freeform",
  "tags": ["memory-management", "virtual-memory"],
  "answer": "The correct advantages/disadvantages go here (from solutions file).",
  "llm_judge_instructions": "Award 1 point for identifying a valid advantage (e.g., smaller page table, reduced metadata overhead) and 1 point for identifying a valid disadvantage (e.g., processes cannot use all physical memory, potential fragmentation). Award 0 points if either part is missing or incorrect."
}
```

---

## Question 3a [6 point(s)]

3a. (6 marks)

void bump(){
  int y;
  x++; // x is a global variable
  y = x;
  kprintf("%d", y); // print value of y
}

Consider that x is a volatile global integer initialized to 0 before any calls to bump, and that the bump function is part of a concurrent program with k concurrent threads, each calling bump once. Assume kprintf is atomic (prints one at a time).

Suppose that this concurrent program is running on a machine with one single-core processor, and that k = 4. Which of the following outputs are possible for this program? Write "yes" next to each output that is possible, and "no" next to each output that is not possible. Note that you must get at least half of these correct to receive any credit for your answer.

- 1234
- 4321
- 0123
- 2222
- 4444
- 1235
- 012
- 1124

```json
{
  "problem_id": "3a",
  "points": 6,
  "type": "Freeform",
  "tags": ["concurrency", "shared-memory"],
  "answer": "The correct yes/no sequence goes here (from solutions file).",
  "llm_judge_instructions": "Award 1 point for each correct yes/no determination, up to 6 points total. Provide partial credit for partially correct sequences accordingly."
}
```

---

## Question 3b [2 point(s)]

3b. (2 marks)

Suppose instead that the concurrent program (with k = 4) runs on a machine with two single-core processors. Do your answers from part (a) change? If not, write "No Change". If so, indicate one output string from part (a) for which you would give a different answer in this situation.

```json
{
  "problem_id": "3b",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "multiprocessing"],
  "answer": "\"No Change\"",
  "llm_judge_instructions": "Award full credit (2 points) if the response is exactly \"No Change\" when appropriate. If a different output string would change, award full credit for correctly identifying one such string and explaining why."
}
```

---

## Question 4a [3 point(s)]

4a. (3 marks)

Virtual Address  Physical Address
0x0008           0AF0
0x0010           1AF0
0x0000           2224
0x0008           3224
0x0007           3234
0x0018           3234

Suppose that while a process P is running, it uses the virtual addresses shown in the left column of the table above. For each of these virtual addresses, the corresponding physical address (after address translation) is also shown in the table. On the machine on which P is running, both virtual addresses and physical addresses are 32 bits long.

Given the virtual-to-physical address translations shown in the table, is it possible that the MMU used dynamic relocation to translate P’s virtual addresses to physical addresses? If so, write “YES” and indicate the value that must be in the MMU’s relocation register while P is running. If not, write “NO” and explain, briefly and clearly, how you know that dynamic relocation was not used.

```json
{
  "problem_id": "4a",
  "points": 3,
  "type": "Freeform",
  "tags": ["memory-management", "relocation"],
  "answer": "NO.",
  "llm_judge_instructions": "Award 3 points if the answer correctly explains that dynamic relocation cannot explain the translations because the translation offset is not consistent across the given addresses (i.e., the required relocation register value would have to be different for different addresses). Provide 0 points otherwise."
}
```

---

## Question 4b [3 point(s)]

4b. (3 marks)

Is it possible that the MMU used paging, with a page size of 64 KB (2^16 bytes), to translate P’s virtual addresses to physical addresses? If so, write “YES”. If not, write “NO” and explain, briefly and clearly, how you know that paging with this page size was not used.

```json
{
  "problem_id": "4b",
  "points": 3,
  "type": "Freeform",
  "tags": ["memory-management", "paging"],
  "answer": "NO.",
  "llm_judge_instructions": "Award 3 points if the answer correctly explains that paging with 64 KB pages would require identical 16-bit offsets in virtual and physical addresses for each mapping, which is not observed in the provided translations. Provide 0 points otherwise."
}
```

---

## Question 4c [2 point(s)]

4c. (2 marks)

Is it possible that the MMU used paging, with a page size of 4 KB (2^12 bytes), to translate P’s virtual addresses to physical addresses? If so, write “YES”. If not, write “NO” and explain, briefly and clearly, how you know that paging with this page size was not used.

```json
{
  "problem_id": "4c",
  "points": 2,
  "type": "Freeform",
  "tags": ["memory-management", "paging"],
  "answer": "YES.",
  "llm_judge_instructions": "Award 2 points if the answer correctly explains that paging with 4 KB pages could explain the translations because the 12-bit offsets match between the virtual and physical addresses where required. Provide 0 points otherwise."
}
```

---

## Question 5a [3 point(s)]

5a. (3 marks)

Is it possible for a thread’s kernel stack to contain more than one trap frame? If yes, write “YES” and identify — clearly and briefly — a situation in which this could occur. If not, write “NO”.

```json
{
  "problem_id": "5a",
  "points": 3,
  "type": "Freeform",
  "tags": ["kernel-stack", "trapframe"],
  "answer": "YES.",
  "llm_judge_instructions": "Award up to 3 points for a correct scenario: 2 points for describing a valid situation (e.g., an interrupt or exception occurring while the thread is already in kernel mode producing a nested trapframe, or a trap occurring while handling another trap), and 1 point for a brief clear explanation of why multiple trapframes can accumulate on the kernel stack."
}
```

---

## Question 5b [2 point(s)]

5b. (2 marks)

Is it possible that a call to OS/161’s wchan sleep function will cause a thread context switch? Answer “YES” or “NO” and briefly explain your answer. (Answers without a clear explanation will receive no credit.)

```json
{
  "problem_id": "5b",
  "points": 2,
  "type": "Freeform",
  "tags": ["os161", "sleep", "context-switch"],
  "answer": "YES.",
  "llm_judge_instructions": "Award 2 points if the answer explains that calling wchan_sleep makes the thread block (not runnable) and the scheduler will choose another thread to run, thereby causing a context switch; award 0 points otherwise."
}
```

---

## Question 5c [2 point(s)]

5c. (2 marks)

Each page table entry normally includes a valid bit. Explain, briefly and clearly, the purpose of a valid bit. What happens if a process attempts to access a virtual address on a page that is mapped by an invalid page table entry, i.e., one for which the valid bit is not set. Again, explain briefly and clearly.

```json
{
  "problem_id": "5c",
  "points": 2,
  "type": "Freeform",
  "tags": ["memory-management", "pagetable"],
  "answer": "Valid bits indicate which pages are allowed to be used; accessing an invalid page typically triggers an exception that the kernel must handle.",
  "llm_judge_instructions": "Award 2 points for a concise correct explanation: 1 point for stating the purpose of the valid bit (marks whether the mapping is present/allowed), and 1 point for stating that access causes a page fault/exception which the kernel handles (e.g., by loading the page or terminating the process)."
}
```

---

## Question 5d [3 point(s)]

5d. (3 marks)

When a system call occurs in OS/161, how does the kernel know which system call has been requested? Explain briefly and clearly.

```json
{
  "problem_id": "5d",
  "points": 3,
  "type": "Freeform",
  "tags": ["os161", "system-call"],
  "answer": "The system call code is placed in a designated register (e.g., v0/R2) before entering the kernel; the kernel reads this code to determine which system call was requested.",
  "llm_judge_instructions": "Award 3 points for a correct brief explanation describing the use of a designated register (e.g., R2/v0) or designated location where the syscall number is passed to the kernel and how the kernel uses it to dispatch the requested system call. Partial credit as appropriate."
}
```

---

## Question 6a [3 point(s)]

6a. (3 marks)

List the different transitions between the 3 thread states. Why can’t a thread go from a blocked state directly to a running state?

```json
{
  "problem_id": "6a",
  "points": 3,
  "type": "Freeform",
  "tags": ["thread-states", "scheduling"],
  "answer": "The transitions listed are correct and the explanation is as given.",
  "llm_judge_instructions": "Award a total of 3 points as follows: 2 points for correctly identifying the three transitions between Ready, Running, and Blocked (award 2 points if all three are correct, 1 point if two are correct, 0 if fewer), and 1 point for a clear explanation why a blocked thread cannot go directly to running (e.g., the scheduler must move it to the ready queue and choose it via dispatch; direct transition would circumvent scheduling and possible locking semantics)."
}
```

---

## Question 6b [2 point(s)]

6b. (2 marks)

Explain the difference between a trapframe and a switchframe. What generates a trapframe? What generates a switchframe?

```json
{
  "problem_id": "6b",
  "points": 2,
  "type": "Freeform",
  "tags": ["trapframe", "switchframe"],
  "answer": "A trapframe is produced by exceptions/interrupts/syscalls; a switchframe is produced by thread yield/switch. The trapframe stores registers that must be saved across the exception; the switchframe may omit non-preserved registers.",
  "llm_judge_instructions": "Award 2 points: 1 point for correctly describing the trapframe and what generates it (interrupt/exception/syscall), and 1 point for correctly describing the switchframe and what generates it (thread yield/thread switch)."
}
```

---

## Question 6c [3 point(s)]

6c. (3 marks)

Describe a scenario (list of steps) in which having spinlock_release(&sem->semlock) before wchan_lock(sem->semwchan) in the semaphore P() implementation can cause a concurrency problem.

```json
{
  "problem_id": "6c",
  "points": 3,
  "type": "Freeform",
  "tags": ["semaphore", "synchronization"],
  "answer": "A detailed sequence where releasing the semlock before acquiring the wchan lock allows a wakeup to occur while the waiting thread is not yet blocked, leading to a lost wakeup scenario and potential indefinite sleep.",
  "llm_judge_instructions": "Award up to 3 points: 2 points for a clear step-by-step scenario showing the race (e.g., thread A observes count==0 and releases semlock; before A acquires wchan lock, thread B does V() and wakes; A then sleeps on wchan and misses the wakeup), and 1 point for explicitly explaining that this leads to a lost wakeup or potential indefinite sleep. Award 0 points for an incorrect or missing explanation."
}
```

---

## Question 6d [2 point(s)]

6d. (2 marks)

What information can be found in each TLB entry?

```json
{
  "problem_id": "6d",
  "points": 2,
  "type": "Freeform",
  "tags": ["tlb", "memory-management"],
  "answer": "Page number and frame number (plus any additional fields if applicable in the hardware, but core information is page/frame).",
  "llm_judge_instructions": "Award 2 points for mentioning the page (virtual page number) to frame (physical frame number) mapping. Optionally mention additional fields (valid, dirty, permission bits) for full credit."
}
```

---

## Question 7 [12 point(s)]

7. (12 total marks)

You have been hired by Snowflake Entertainment to design the matchmaking system for their new multiplayer online game. In this game, a match consists of 3 players and can only start when all 3 players are available. The company owns only one server and the server can only host one match at a time. A new match can start on the server only when (a) the previous match has finished, and (b) three players are available.

Implement the following three functions to satisfy the specified constraints. Global variables can be defined in the provided space. Your implementation should ensure that exactly three players are grouped per match, matches do not overlap on the single server, and waiting/wakeup behavior is correct. Show global declarations/initialization, before_match (blocks until the player's match can start) and after_match (called when the player's match finishes).

(Provide your synchronization code using locks and condition variables; do not include solutions here.)

```json
{
  "problem_id": "7",
  "points": 12,
  "type": "Freeform",
  "tags": ["concurrency", "synchronization", "locks", "cv"],
  "answer": "An implementation description or code that satisfies the synchronization constraints.",
  "llm_judge_instructions": "Award up to 12 points with the following breakdown: 4 points for correct and complete global variables and initialization (locks, cvs, counters); 4 points for a correct before_match implementation that blocks and only allows groups of exactly 3 to start a match when the server is free; 4 points for a correct after_match implementation that releases the server and wakes up the next group when appropriate. Deduct points for lost wakeups, races, or allowing overlapping matches."
}
```