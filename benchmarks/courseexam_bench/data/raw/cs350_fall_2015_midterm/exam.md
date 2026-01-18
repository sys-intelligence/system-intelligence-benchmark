# CS350 Fall 2015 Midterm

```json
{
  "exam_id": "cs350_fall_2015_midterm",
  "test_paper_name": "CS350 Fall 2015 Midterm",
  "course": "CS350",
  "institution": "University of Waterloo",
  "year": 2015,
  "score_total": 70,
  "num_questions": 19
}
```

---

## Question 1 [12 point(s)]

Consider a concurrent program that uses three semaphores sa, sb, and sc initialized as follows (initialization code is executed once by the initial thread). Two functions, func1 and func2, are run by many threads (some threads run func1, others run func2). func1 calls funcA(), and func2 calls funcB(). The original semaphore-based code is:

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

Re-implement func1 and func2, and any required global variables and initialization/cleanup, using locks and condition variables (no semaphores) so that the behavior is equivalent to the semaphore-based version. Show global declarations and initialization (called once before threads start) and cleanup (called once when done), and implementations of func1 and func2. Your code should compile conceptually against an OS/161-like API with lock_acquire/lock_release and cv_wait/cv_signal/cv_broadcast.

```json
{
  "problem_id": "1",
  "points": 12,
  "type": "Freeform",
  "tags": ["synchronization","semaphores","locks","condition-variables"],
  "answer": "",
  "llm_judge_instructions": "Total 12 pts. Award 3 pts for correct and complete global declarations and initialization (including any counters or state variables needed). Award 1 pt for providing appropriate cleanup code. Award 4 pts for a correct implementation of func1 that preserves ordering/synchronization equivalent to the semaphore version (correct use of lock(s), cv wait/signal, and counter/state). Award 4 pts for a correct implementation of func2 that preserves equivalent behavior. Partial credit: subtract points for missing lock protection, incorrect condition checks, lost wakeups, or use of semaphores. Full points only if implementation enforces same ordering constraints as the original semaphore code."
}
```

---

## Question 2a [2 point(s)]

a. What is the maximum number of entries in a page table in this system? (Explain briefly if helpful.)

```json
{
  "problem_id": "2a",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory","paging","memory-management"],
  "answer": "",
  "llm_judge_instructions": "2 pts total. Award 2 pts if the answer is exactly 16 (or 0x10) or states 2^4 = 16. Award 1 pt if the student gives a correct reasoning about page-number bits (e.g., identifies 4 page-number bits) but does not compute the final numeric answer correctly."
}
```

---

## Question 2b [4 point(s)]

b. A process P1 has the following page table. Frame numbers are in hexadecimal.
Page Number -> Frame Number:
00 -> 0x1010
10 -> 0x2034
20 -> 0x43AC
30 -> 0x1100
40 -> 0xAC11
50 -> 0x8000

For each of the following physical addresses, indicate the virtual address that maps to it for P1. If the physical address is not part of the physical memory assigned to P1, write NO TRANSLATION. Use hexadecimal notation for virtual addresses.
- 0x1100A0
- 0xAC1100
- 0xBA3424
- 0x43ACA0
- 0x3A0
- 0x400
- 0x2A0

```json
{
  "problem_id": "2b",
  "points": 4,
  "type": "Freeform",
  "tags": ["virtual-memory","paging","address-translation"],
  "answer": "",
  "llm_judge_instructions": "4 pts total. Award 1 point for each correctly translated physical address, up to 4 points total (identify the correct virtual address in hex or write NO TRANSLATION correctly). If more than four are correct, cap at 4. No penalty beyond incorrect translations."
}
```

---

## Question 2c [2 point(s)]

c. Due to a bug, the following is the page table of P1's child immediately after fork. Based only on copy-on-write semantics of a typical fork implementation, mark entries you are certain are incorrect. Page table:
Page Number -> Frame Number:
00 -> 0x2453
10 -> 0x1010
20 -> 0xEA35
30 -> 0x3100
40 -> 0x2034
50 -> 0x9012

Which entries can you be certain are incorrect? Identify them (by page number).

```json
{
  "problem_id": "2c",
  "points": 2,
  "type": "Freeform",
  "tags": ["os-161","paging"],
  "answer": "",
  "llm_judge_instructions": "2 pts total. Award 1 point for each correctly identified page table entry that must be incorrect given a correct copy-on-write/fork behavior (i.e., entries that could not result from copying the parent's frames). Full credit if both certainly-incorrect entries are identified; 1 pt if only one is identified; 0 otherwise."
}
```

---

## Question 2d [2 point(s)]

d. Name one advantage and one disadvantage of having a virtual address space that is smaller than the physical address space.

```json
{
  "problem_id": "2d",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory","paging"],
  "answer": "",
  "llm_judge_instructions": "2 pts total. Award 1 pt for a valid advantage (e.g., smaller page table, less per-process metadata). Award 1 pt for a valid disadvantage (e.g., process cannot use all physical memory, potential wasted physical memory or address space exhaustion)."
}
```

---

## Question 3a [6 point(s)]

a. Suppose this concurrent program runs on a machine with one single-core processor and k = 4. For each of the following outputs, write “yes” if that output is possible, and “no” if it is not possible. (Answer yes/no for each listed output.)
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
  "tags": ["concurrency","race-conditions","scheduling"],
  "answer": "",
  "llm_judge_instructions": "6 pts total. Award 1 point for each correct yes/no classification for the first six outputs in the list (1234, 4321, 0123, 2222, 4444, 1235). If those six are all correct, award full 6 pts. Do not grade the last three outputs (012, 1124) for points. Partial credit given proportionally (1 pt per correct classification among the first six)."
}
```

---

## Question 3b [2 point(s)]

b. Suppose instead the concurrent program with k = 4 runs on a machine with two single-core processors. Do your answers from part (a) change? If not, write "No Change". If so, give one output string from part (a) for which your yes/no answer would change, and explain briefly.

```json
{
  "problem_id": "3b",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency","multiprocessing","scheduling"],
  "answer": "",
  "llm_judge_instructions": "2 pts total. Award 2 pts if the student correctly states either 'No Change' with brief justification or identifies a single output whose classification would change and provides a correct brief explanation. Award 1 pt for a partially correct reasoning."
}
```

---

## Question 4a [3 point(s)]

a. Given a set of virtual-to-physical address translations for process P (provided on the exam sheet), is it possible that the MMU used dynamic relocation (base register) to translate P's virtual addresses to physical addresses? If so, write YES and indicate the relocation register value; if not, write NO and briefly explain why not (one or two sentences).

```json
{
  "problem_id": "4a",
  "points": 3,
  "type": "Freeform",
  "tags": ["memory-management","mmu","relocation"],
  "answer": "",
  "llm_judge_instructions": "3 pts total. Award 2 pts for correctly answering NO (if a single relocation value cannot produce all translations) or YES with a correct relocation value. Award 1 additional point for a correct brief explanation (e.g., explaining that all translations must use the same r and showing a counterexample)."
}
```

---

## Question 4b [3 point(s)]

b. Is it possible that the MMU used paging with a page size of 64 KB (2^16 bytes) to translate P's virtual addresses to physical addresses? If so, write YES; if not, write NO and briefly explain why paging with that page size cannot have been used (one or two sentences).

```json
{
  "problem_id": "4b",
  "points": 3,
  "type": "Freeform",
  "tags": ["memory-management","paging"],
  "answer": "",
  "llm_judge_instructions": "3 pts total. Award 2 pts for correctly answering NO (if offsets differ) or YES if offsets are consistent. Award 1 pt for a concise correct explanation referencing page offset equality or mismatch."
}
```

---

## Question 4c [2 point(s)]

c. Is it possible that the MMU used paging with a page size of 4 KB (2^12 bytes) to translate P's virtual addresses to physical addresses? If so, write YES; if not, write NO and briefly justify.

```json
{
  "problem_id": "4c",
  "points": 2,
  "type": "Freeform",
  "tags": ["memory-management","paging"],
  "answer": "",
  "llm_judge_instructions": "2 pts total. Award 2 pts for YES if the student gives a correct justification that 4 KB pages produce consistent 12-bit offsets in the examples, or 0 pts if incorrect. Partial credit (1 pt) for correct partial reasoning about offsets."
}
```

---

## Question 5a [3 point(s)]

a. Is it possible for a thread's kernel stack to contain more than one trapframe? If yes, write YES and briefly describe a situation in which this could occur. If not, write NO and explain.

```json
{
  "problem_id": "5a",
  "points": 3,
  "type": "Freeform",
  "tags": ["kernel","trapframe","interrupt"],
  "answer": "",
  "llm_judge_instructions": "3 pts total. Award 2 pts for correctly answering YES (if that is correct) and describing a concrete scenario (e.g., an interrupt occurs while handling a system call). Award 1 pt for a concise explanation of why multiple trapframes can be present. Partial credit for plausible scenarios."
}
```

---

## Question 5b [2 point(s)]

b. Can a call to OS/161's wchan_sleep function cause a thread context switch? Answer YES or NO and briefly explain.

```json
{
  "problem_id": "5b",
  "points": 2,
  "type": "Freeform",
  "tags": ["os-161","sleep","scheduler"],
  "answer": "",
  "llm_judge_instructions": "2 pts total. Award 2 pts for YES with a concise correct explanation that the sleeping thread is descheduled and the scheduler selects another thread to run. Award 1 pt for partially correct reasoning."
}
```

---

## Question 5c [2 point(s)]

c. Each page table entry normally includes a valid bit. Briefly explain the purpose of the valid bit and what happens if a process attempts to access a virtual address whose page table entry has the valid bit unset.

```json
{
  "problem_id": "5c",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging","tlb","mmu"],
  "answer": "",
  "llm_judge_instructions": "2 pts total. Award 2 pts for stating that the valid bit indicates whether the page mapping is present/usable and that accessing an invalid page causes an exception/page fault which the kernel must handle. Award 1 pt for partial or imprecise descriptions."
}
```

---

## Question 5d [3 point(s)]

d. When a system call occurs in OS/161, how does the kernel know which system call has been requested? Explain briefly.

```json
{
  "problem_id": "5d",
  "points": 3,
  "type": "Freeform",
  "tags": ["os-161","system-call","kernel"],
  "answer": "",
  "llm_judge_instructions": "3 pts total. Award 2 pts for stating that the user program places a syscall number/code in a designated register and the kernel's syscall handler reads it. Award 1 pt for identifying the typical register used (e.g., v0/R2) or equivalent platform-specific register."
}
```

---

## Question 6a [3 point(s)]

a. List the different transitions among the three thread states (Ready, Running, Blocked). Why can't a thread go directly from Blocked to Running? Explain briefly.

```json
{
  "problem_id": "6a",
  "points": 3,
  "type": "Freeform",
  "tags": ["thread-states","scheduler"],
  "answer": "",
  "llm_judge_instructions": "3 pts total. Award 2 pts for listing the four transitions (Ready→Running, Running→Ready, Running→Blocked, Blocked→Ready). Award 1 pt for a clear explanation that Blocked→Running is not allowed because the scheduler must dispatch the thread from Ready to Running and to avoid bypassing scheduler invariants and synchronization (e.g., the thread must be made Ready first)."
}
```

---

## Question 6b [2 point(s)]

b. Explain the difference between a trapframe and a switchframe. What generates a trapframe? What generates a switchframe?

```json
{
  "problem_id": "6b",
  "points": 2,
  "type": "Freeform",
  "tags": ["trapframe","switchframe","kernel"],
  "answer": "",
  "llm_judge_instructions": "2 pts total. Award 1 pt for describing the difference (trapframe: full CPU state for exceptions/interrupts/syscalls; switchframe: minimal saved state for context switch). Award 1 pt for correctly identifying generators (trapframe generated by exceptions/interrupts/syscalls; switchframe generated by thread context switches/yield)."
}
```

---

## Question 6c [3 point(s)]

c. Describe a scenario (step-by-step) in which releasing a semaphore's spinlock before acquiring the wchan lock in the semaphore P() implementation can cause a concurrency problem. Explain the possible bad outcome.

```json
{
  "problem_id": "6c",
  "points": 3,
  "type": "Freeform",
  "tags": ["semaphore","concurrency","synchronization"],
  "answer": "",
  "llm_judge_instructions": "3 pts total. Award 2 pts for a correct step-by-step scenario showing the race (e.g., thread A sees count==0, releases spinlock, is preempted; thread B does V(), increments count and wakes a waiter; thread A then acquires wchan lock and sleeps despite count>0). Award 1 pt for stating the bad outcome (lost wakeup or indefinite sleep). Partial credit for partial but correct reasoning."
}
```

---

## Question 6d [2 point(s)]

d. What information is typically stored in each TLB entry?

```json
{
  "problem_id": "6d",
  "points": 2,
  "type": "Freeform",
  "tags": ["tlb","memory-management"],
  "answer": "",
  "llm_judge_instructions": "2 pts total. Award 2 pts for naming both the virtual page number and the corresponding physical frame number (and optionally permission/flags). Award 1 pt for naming one of the two."
}
```

---

## Question 7 [12 point(s)]

You are designing a matchmaking system for a multiplayer game. A match consists of 3 players and can only start when all 3 players are available. The system owns one server that can host only one match at a time. A new match can start only when (a) the previous match has finished, and (b) three players are available. Implement synchronization to meet these constraints.

Provide global variable declarations and implementations of the following functions (called from player threads and system initialization/cleanup):
- void game_sync_init(void);        // called once before any players arrive
- void game_sync_cleanup(void);     // called once when system is taken down
- void before_match(void);          // called once by each player before that player's match; should block until the player's match can start
- void after_match(void);           // called once by each player after that player's match is finished

You may define global locks, condition variables, and counters. Do not provide any extra output or debugging prints in your synchronization code. Your implementation should ensure exactly three players start a match together, only one match runs on the server at a time, and waiting players are properly awakened to form subsequent matches.

```json
{
  "problem_id": "7",
  "points": 12,
  "type": "Freeform",
  "tags": ["synchronization","concurrency","condition-variables"],
  "answer": "",
  "llm_judge_instructions": "12 pts total. Award 3 pts for correct and complete global variables and initialization (including any counters and creation of lock/cv). Award 1 pt for correct cleanup. Award 4 pts for correct before_match implementation (blocks until exactly 3 players form a match and ensures only one match runs at a time, and releases players to start together). Award 4 pts for correct after_match implementation (decrements in-game count, and if necessary wakes waiting players to start the next match). Deduct points for lost wakeups, incorrect condition checks, or allowing more than one concurrent match."
}
```

---