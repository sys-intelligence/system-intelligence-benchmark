# CS 350 Fall 2015 Midterm

```json
{
  "exam_id": "cs350_fall_2015_midterm",
  "test_paper_name": "CS 350 Fall 2015 Midterm",
  "course": "CS 350",
  "institution": "University of Waterloo",
  "year": 2015,
  "score_total": 70,
  "num_questions": 19
}
```

---

## Question 1 [12 point(s)]

Global Variables
Initialization
Function func1
Function func2

The following concurrent program uses semaphores:

```c
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
```

Suppose the initialization code is executed once by the program's initial thread. The initial thread then creates many new threads; some run func1 and some run func2. func1 and func2 call funcA and funcB respectively (not shown).

Re-implement func1 and func2 without using semaphores. Use locks and condition variables for synchronization. Your re-implemented functions must have the same synchronization behavior as the original semaphore-based versions. Show any global variable declarations and initialization code, and provide implementations of func1 and func2.

Do not include solutions or commentary in your submission — only your re-implementation code and any needed global declarations/initialization.

```json
{
  "problem_id": "1",
  "points": 12,
  "type": "Freeform",
  "tags": ["concurrency","synchronization","semaphores"],
  "answer": "",
  "llm_judge_instructions": "Allocate 12 points as follows: 3 pts for correct global declarations and initialization showing locks, condition variable(s), and any counters; 4 pts for func1 implementation that correctly enforces mutual exclusion for funcA (equivalent to P(sa)/V(sa)) and the wait-on-sc semantics (equivalent to P(sc)); 4 pts for func2 implementation that correctly enforces mutual exclusion for funcB (equivalent to P(sb)/V(sb)) and the V(sc) semantics (waking any waiter(s) appropriately); 1 pt for avoiding lost-wakeup or race conditions (proper ordering of lock/acquire/release and cv wait/signal usage). Award points only if the code reproduces the original ordering and waiting semantics of the semaphore solution."
}
```

---

## Question 2a [2 point(s)]

a. (2 marks) What is the maximum number of entries in a page table in this system?

```json
{
  "problem_id": "2a",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging","virtual-memory"],
  "answer": "",
  "llm_judge_instructions": "Award 2 points for the correct numeric answer. Accept answers that show the calculation (e.g., number of virtual pages = 2^(virtual-address-bits - page-offset-bits)). Award full credit only for the correct final value."
}
```

---

## Question 2b [4 point(s)]

b. (4 marks)

A process P1 has the following page table. Frame numbers are given in hexadecimal.

Page Number -> Frame Number
- 0x0 -> 0x1010
- 0x1 -> 0x2034
- 0x2 -> 0x43AC
- 0x3 -> 0x1100
- 0x4 -> 0xAC11
- 0x5 -> 0x8000

For each of the following physical addresses, indicate the virtual address to which it maps. If the physical address is not part of the physical memory assigned to P1, write NO TRANSLATION. Use hexadecimal notation for the virtual addresses.

Physical addresses to translate:
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
  "llm_judge_instructions": "Award 1 point for each correct translation or correct NO TRANSLATION for the listed physical addresses (4 addresses worth 1 point each). Require correct hexadecimal virtual address formatting when a translation exists."
}
```

---

## Question 2c [2 point(s)]

c. (2 marks)

Due to a bug in the OS/161 as_copy function, the following is the page table of P1’s child process immediately after it returns from fork. Mark the entries in the page table that you are certain to be incorrect.

Page Number -> Frame Number
- 0x0 -> 0x2453
- 0x1 -> 0x1010
- 0x2 -> 0xEA35
- 0x3 -> 0x3100
- 0x4 -> 0x2034
- 0x5 -> 0x9012

Identify which page table entries (by page number) are certainly incorrect after fork (list page numbers).

```json
{
  "problem_id": "2c",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory","paging","os161"],
  "answer": "",
  "llm_judge_instructions": "Award up to 2 points: 1 point for each correctly identified page number that must be incorrect due to the fork/copy semantics (list the specific page numbers). Partial credit allowed (1 point) if one correct page number is identified; 2 points only if both incorrect entries expected are correctly listed."
}
```

---

## Question 2d [2 point(s)]

d. (2 marks)

Name one advantage and one disadvantage of having a virtual address space that is smaller than the physical address space.

```json
{
  "problem_id": "2d",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory","address-space"],
  "answer": "",
  "llm_judge_instructions": "Award 1 point for a correct advantage (e.g., smaller page tables, simpler address-space management) and 1 point for a correct disadvantage (e.g., some physical memory cannot be addressed/used by the process). Each distinct, relevant statement earns the corresponding point."
}
```

---

## Question 3a [6 point(s)]

a. (6 marks)

Suppose that this concurrent program is running on a machine with one single-core processor, and that k = 4. Which of the following outputs are possible for this program? For each listed output, write “yes” if it is possible and “no” if it is not possible. (You must get at least half of the individual labels correct to receive any credit for this part.)

List of outputs:
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
  "tags": ["concurrency","races","threading"],
  "answer": "",
  "llm_judge_instructions": "There are 8 items. To receive any credit, at least 4 of the 8 labels must be correct. If fewer than 4 are correct, award 0 points. If at least 4 are correct, award 0.75 points for each correctly labeled output (0.75 * number_correct), up to a maximum of 6 points. Provide brief justification for any 'no' answers if the labeling is non-obvious."
}
```

---

## Question 3b [2 point(s)]

b. (2 marks)

Suppose instead that the concurrent program (with k = 4) runs on a machine with two single-core processors. Do your answers from part (a) change? If not, write “No Change”. If so, indicate one output string from part (a) for which you would give a different answer in this situation and briefly explain why.

```json
{
  "problem_id": "3b",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency","multicore"],
  "answer": "",
  "llm_judge_instructions": "Award 2 points for a correct and concise response: if 'No Change' is correct, award 2 points for that answer with brief justification; if one output changes, award 2 points for correctly identifying one specific output whose possibility changes and providing a correct brief explanation. Partial credit (1 point) may be given for a partially correct explanation."
}
```

---

## Question 4a [3 point(s)]

a. (3 marks)

Given the virtual-to-physical address translations shown in the table (provided on the exam sheet), is it possible that the MMU used dynamic relocation to translate P’s virtual addresses to physical addresses? If so, write “YES” and indicate the value that must be in the MMU’s relocation register while P is running. If not, write “NO” and explain briefly how you know dynamic relocation was not used.

```json
{
  "problem_id": "4a",
  "points": 3,
  "type": "Freeform",
  "tags": ["virtual-memory","relocation"],
  "answer": "",
  "llm_judge_instructions": "Award 3 points total: 2 pts for the correct YES/NO answer, and 1 pt for a concise, correct justification. If YES, provide the relocation value r and show it is consistent with all translations. If NO, explain why a single relocation offset cannot account for all translations."
}
```

---

## Question 4b [3 point(s)]

b. (3 marks)

Is it possible that the MMU used paging, with a page size of 64 KB (2^16 bytes), to translate P’s virtual addresses to physical addresses? If so, write “YES”. If not, write “NO” and explain briefly how you know that paging with this page size was not used.

```json
{
  "problem_id": "4b",
  "points": 3,
  "type": "Freeform",
  "tags": ["paging","page-size"],
  "answer": "",
  "llm_judge_instructions": "Award 3 points: 2 pts for the correct YES/NO answer and 1 pt for a clear explanation referencing the page-offset consistency required by 64 KB pages (i.e., lower 16 bits must match). Full credit only if the explanation correctly links the provided translations to the page-offset criterion."
}
```

---

## Question 4c [2 point(s)]

c. (2 marks)

Is it possible that the MMU used paging, with a page size of 4 KB (2^12 bytes), to translate P’s virtual addresses to physical addresses? If so, write “YES”. If not, write “NO” and explain briefly.

```json
{
  "problem_id": "4c",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging","page-size"],
  "answer": "",
  "llm_judge_instructions": "Award 2 points: 1 pt for the correct YES/NO answer and 1 pt for a brief correct justification based on 4 KB page-offset consistency (lower 12 bits matching where required)."
}
```

---

## Question 5a [3 point(s)]

a. (3 marks)

Is it possible for a thread’s kernel stack to contain more than one trap frame? If yes, write “YES” and identify clearly and briefly a situation in which this could occur. If not, write “NO”.

```json
{
  "problem_id": "5a",
  "points": 3,
  "type": "Freeform",
  "tags": ["kernel","trapframe","interrupts"],
  "answer": "",
  "llm_judge_instructions": "Award 3 points for a correct YES/NO and a clear example. If YES, give a concrete scenario (e.g., thread performs a system call, then an interrupt occurs before the system call handler returns) and explain why multiple trap frames would then appear. Allocate 2 pts for the correct answer and 1 pt for a correct scenario explanation."
}
```

---

## Question 5b [2 point(s)]

b. (2 marks)

Is it possible that a call to OS/161’s wchan_sleep function will cause a thread context switch? Answer “YES” or “NO” and briefly explain your answer.

```json
{
  "problem_id": "5b",
  "points": 2,
  "type": "Freeform",
  "tags": ["os161","sleep","scheduling"],
  "answer": "",
  "llm_judge_instructions": "Award 2 points for the correct YES/NO answer and a brief explanation. Full credit (2 pts) requires: YES plus explanation that wchan_sleep blocks the calling thread and the scheduler will select another runnable thread, causing a context switch."
}
```

---

## Question 5c [2 point(s)]

c. (2 marks)

Each page table entry normally includes a valid bit. Explain briefly the purpose of a valid bit. What happens if a process attempts to access a virtual address on a page that is mapped by an invalid page table entry (i.e., the valid bit is not set)?

```json
{
  "problem_id": "5c",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging","page-table","valid-bit"],
  "answer": "",
  "llm_judge_instructions": "Award 2 points: 1 pt for correctly describing the purpose of the valid bit (indicates whether the mapping is currently valid/usable), and 1 pt for stating the consequence (access triggers an MMU exception/page fault to be handled by the kernel)."
}
```

---

## Question 5d [3 point(s)]

d. (3 marks)

When a system call occurs in OS/161, how does the kernel know which system call has been requested? Explain briefly and clearly.

```json
{
  "problem_id": "5d",
  "points": 3,
  "type": "Freeform",
  "tags": ["os161","system-call","calling convention"],
  "answer": "",
  "llm_judge_instructions": "Award 3 points for correctly stating that the user program places the system call code in a designated register (e.g., v0 or r2 depending on the architecture) before the trap, and that the kernel's syscall handler reads that register to dispatch the appropriate syscall. Allocate 2 pts for identifying the register and 1 pt for explaining the dispatch usage."
}
```

---

## Question 6a [3 point(s)]

a. (3 marks)

List the different transitions between the 3 thread states (Running, Ready, Blocked). Why can’t a thread go from a Blocked state directly to a Running state?

```json
{
  "problem_id": "6a",
  "points": 3,
  "type": "Freeform",
  "tags": ["thread-states","scheduling"],
  "answer": "",
  "llm_judge_instructions": "Award 3 points: 1 pt for listing each of the three basic transitions (Ready→Running, Running→Ready, Running→Blocked) and 1 pt for explaining why Blocked→Running cannot happen directly (must transition to Ready and be scheduled; to prevent bypassing the scheduler and to maintain proper synchronization). If all transitions plus reason are correct, award full credit."
}
```

---

## Question 6b [2 point(s)]

b. (2 marks)

Explain the difference between a trapframe and a switchframe. What generates a trapframe? What generates a switchframe?

```json
{
  "problem_id": "6b",
  "points": 2,
  "type": "Freeform",
  "tags": ["trapframe","switchframe","context-switch"],
  "answer": "",
  "llm_judge_instructions": "Award 2 points: 1 pt for correctly explaining that a trapframe is created by an exception/interrupt/syscall and saves processor state for the trap entry, and 1 pt for explaining that a switchframe is created by the thread-switching code (e.g., thread_yield/threadsched) to save only the registers needed to resume the thread."
}
```

---

## Question 6c [3 point(s)]

c. (3 marks)

Describe a scenario (list of steps) in which having spinlock_release(&sem->semlock) before wchan_lock(sem->semwchan) in the semaphore P() implementation can cause a concurrency problem. Be specific about the sequence of events that lead to the problem.

```json
{
  "problem_id": "6c",
  "points": 3,
  "type": "Freeform",
  "tags": ["semaphore","deadlock","concurrency"],
  "answer": "",
  "llm_judge_instructions": "Award 3 points for a concrete correct sequence that demonstrates a lost-wakeup or sleeping-while-resource-available problem. Allocate points as: 1 pt for describing initial state (e.g., count == 0), 1 pt for the interleaving sequence that shows the race (release semlock, other thread increments and signals), and 1 pt for the resulting incorrect behavior (e.g., the first thread sleeps despite the resource being available)."
}
```

---

## Question 6d [2 point(s)]

d. (2 marks)

What information can be found in each TLB entry?

```json
{
  "problem_id": "6d",
  "points": 2,
  "type": "Freeform",
  "tags": ["tlb","paging"],
  "answer": "",
  "llm_judge_instructions": "Award 2 points: 1 pt for mentioning the virtual page number (or virtual page identifier) and 1 pt for mentioning the corresponding physical frame number. Additional descriptors such as valid bit, permissions, and ASID may be mentioned for full credit but are not required beyond the two main items."
}
```

---

## Question 7 [12 point(s)]

You have been hired to design a matchmaking system for a multiplayer online game. A match consists of 3 players and can only start when all 3 players are available. The company owns only one server and the server can host only one match at a time. A new match can start on the server only when (a) the previous match has finished, and (b) three players are available.

Implement the following functions to satisfy the specified constraints. You may define global variables in the provided space. Provide correct synchronization using locks/condition variables so that:
- Exactly three players form a match.
- Only one match runs on the server at a time.
- Players block in before_match until their match can start, and after_match is called once by each player when their match finishes.

You need only submit the synchronization-related code (global variables, initialization, before_match, after_match, cleanup). Do not include any explanatory text or solution commentary.

The exam sheet provides the function prototypes and comments. Implement them accordingly.

```c
#define PLAYERS_PER_MATCH 3

// Define your global variables here.

// Called only once before any players have arrived.
void game_syncinit(void);

// Called only once when the company takes down the system for maintenance.
void game_synccleanup(void);

// Called once by each player, before that player starts a match
// Should block until the player's match can start
void before_match(void);

// Called once for each player, after that player's match is finished
void after_match(void);
```

```json
{
  "problem_id": "7",
  "points": 12,
  "type": "Freeform",
  "tags": ["synchronization","locks","condition-variables"],
  "answer": "",
  "llm_judge_instructions": "Allocate 12 points as follows: 3 pts for correct global variable declarations and initialization in game_syncinit; 1 pt for correct cleanup in game_synccleanup; 4 pts for a correct before_match implementation that ensures exactly PLAYERS_PER_MATCH players proceed together and that no new match starts until the server is free; 4 pts for a correct after_match implementation that releases the server and wakes up the next group when appropriate. Award points only if solutions avoid race conditions and do not allow more than one match on the server simultaneously. Partial credit allowed per component."
}
```

---