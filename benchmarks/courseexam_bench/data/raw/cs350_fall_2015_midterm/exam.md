# CS350 Fall 2015 Midterm

```json
{
  "exam_id": "cs350_fall_2015_midterm",
  "test_paper_name": "CS350 Fall 2015 Midterm",
  "course": "CS350",
  "institution": "University of Waterloo",
  "year": 2015,
  "score_total": 70,
  "num_questions": 11
}
```

---

## Question 1 [12 point(s)]

Consider the following concurrent program (initialization code is executed once by the initial thread; then many new threads are created, some run func1 and some run func2). The original program uses semaphores as shown:

Global variables / Initialization
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

Re-implement func1 and func2 (including any necessary global variable declarations and initialization) using locks and condition variables (no semaphores). Your re-implemented functions must have the same behavior as the original semaphore-based functions.

```json
{
  "problem_id": "1",
  "points": 12,
  "type": "Freeform",
  "tags": ["concurrency", "synchronization", "locks", "condition-variables"],
  "answer": "A correct re-implementation uses separate locks for protecting funcA and funcB critical sections and a lock+condition variable to implement the signaling behavior of sc, preserving ordering so that func1 waits until func2 signals. For example: declare locks la and lb for funcA and funcB respectively; declare a lock lc, a condition variable cv, and an integer count initialized to 0. func1 acquires la, calls funcA, releases la, then acquires lc, while(count<=0) cv_wait(cv, lc); count--; release lc. func2 acquires lb, calls funcB, releases lb, acquires lc, count++; cv_signal(cv, lc); release lc. (Any equivalent correct implementation that preserves semantics earns full credit.)",
  "llm_judge_instructions": "Total 12 pts: Award 4 pts for correct and complete global declarations and initialization (locks, cv, counter or equivalent). Award 4 pts for a correct func1 implementation preserving mutual exclusion around funcA and waiting behavior equivalent to P(sc). Award 4 pts for a correct func2 implementation preserving mutual exclusion around funcB and signaling behavior equivalent to V(sc). Partial credit: award points proportionally if parts are partially correct; do not award credit for semaphore-based solutions. Implementation must be thread-safe and preserve original ordering semantics."
}
```

---

## Question 2a [2 point(s)]

What is the maximum number of entries in a page table in this system?

```json
{
  "problem_id": "2a",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging", "virtual-memory"],
  "answer": "16",
  "llm_judge_instructions": "Award 2 points for the answer '16'. 0 points for any other answer."
}
```

---

## Question 2b [4 point(s)]

A process P1 has the following page table (frame numbers shown in hexadecimal):

Page Number -> Frame Number
0x0 -> 0x1010
0x1 -> 0x2034
0x2 -> 0x43AC
0x3 -> 0x1100
0x4 -> 0xAC11
0x5 -> 0x8000

For each of the following physical addresses, indicate the virtual address to which it maps. If the physical address is not part of the physical memory assigned to P1, write NO TRANSLATION. Use hexadecimal notation for the virtual addresses.

- 0x1100A0
- 0xAC1100
- 0xBA3424
- 0x43ACA0

```json
{
  "problem_id": "2b",
  "points": 4,
  "type": "Freeform",
  "tags": ["paging", "virtual-memory"],
  "answer": "0x1100A0 -> 0x3A0; 0xAC1100 -> 0x400; 0xBA3424 -> NO TRANSLATION; 0x43ACA0 -> 0x2A0",
  "llm_judge_instructions": "Total 4 pts: Award 1 point for each of the four correct mappings: (0x1100A0 -> 0x3A0), (0xAC1100 -> 0x400), (0xBA3424 -> NO TRANSLATION), (0x43ACA0 -> 0x2A0)."
}
```

---

## Question 2c [2 point(s)]

Due to a bug in the OS/161 as_copy function, the following is the page table of P1’s child process immediately after it returns from fork. Mark the entries in the child page table that you are certain to be incorrect.

Child page table (Page Number -> Frame Number):
0x0 -> 0x2453
0x1 -> 0x1010
0x2 -> 0xEA35
0x3 -> 0x3100
0x4 -> 0x2034
0x5 -> 0x9012

Which entries are certainly incorrect?

```json
{
  "problem_id": "2c",
  "points": 2,
  "type": "Freeform",
  "tags": ["os161", "paging"],
  "answer": "Entries certainly incorrect: 0x1 -> 0x1010 and 0x4 -> 0x2034.",
  "llm_judge_instructions": "Award 1 point for each correctly identified incorrect entry: 0x1 -> 0x1010 and 0x4 -> 0x2034. 0 points for incorrect identifications."
}
```

---

## Question 2d [2 point(s)]

Name one advantage and one disadvantage of having a virtual address space that is smaller than the physical address space.

```json
{
  "problem_id": "2d",
  "points": 2,
  "type": "Freeform",
  "tags": ["memory-management", "virtual-memory"],
  "answer": "Advantage: Smaller page table (less memory used for per-process page tables). Disadvantage: A process cannot directly use all available physical memory; its accessible address range is limited.",
  "llm_judge_instructions": "Award 1 point for a correct advantage and 1 point for a correct disadvantage (total 2 pts). Each part must be a clear, plausible statement about address space size trade-offs."
}
```

---

## Question 3a [6 point(s)]

Consider the function:

void bump(){
  int y;
  x++; // x is a global variable
  y = x;
  kprintf("%d", y); // print value of y
}

Assume x is a volatile global integer initialized to 0 before any calls to bump. Suppose the program uses k concurrent threads, each calling bump once. Calls to kprintf are atomic (i.e., prints do not interleave). For k = 4 running on a single-core processor, which of the following outputs are possible? For each output, write "yes" if possible and "no" if not.

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
  "tags": ["concurrency", "multithreading"],
  "answer": "Possible: 1234 (yes), 4321 (yes), 2222 (yes), 4444 (yes). Not possible: 0123 (no), 1235 (no), 012 (no), 1124 (no).",
  "llm_judge_instructions": "Part a (6 pts): Award 1 point each for the following six correct determinations: 1234 -> yes (1 pt), 4321 -> yes (1 pt), 2222 -> yes (1 pt), 4444 -> yes (1 pt), 0123 -> no (1 pt), 1235 -> no (1 pt). (The other outputs were included for completeness but will not be graded for points in this part.)"
}
```

---

## Question 3b [2 point(s)]

Suppose instead the concurrent program (with k = 4) runs on a machine with two single-core processors. Do your answers from part (a) change? If not, write "No Change". If so, indicate one output string from part (a) for which you would give a different answer and explain briefly.

```json
{
  "problem_id": "3b",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "multithreading"],
  "answer": "No Change",
  "llm_judge_instructions": "Award 2 pts for the answer 'No Change'. If a different answer is given, award 2 pts only if a correct example and brief correct explanation are provided; otherwise 0 pts."
}
```

---

## Question 4 [8 point(s)]

Suppose a process P uses the following virtual addresses (left column) and the corresponding physical addresses (right column) are observed:

Virtual Address -> Physical Address
0x0000 -> 0x2224
0x0007 -> 0x3234
0x0008 -> 0x3224
0x0010 -> 0x1AF0
0x0018 -> 0x3234
0x0008 -> 0x0AF0

(These are the translations observed while P is running. Virtual and physical addresses are 32 bits.)

a. Given the translations shown, is it possible that the MMU used dynamic relocation (i.e., a single relocation register) to translate P’s virtual addresses to physical addresses? If so, write "YES" and indicate the relocation register value. If not, write "NO" and briefly explain why not.

b. Is it possible that the MMU used paging with page size 64 KB (2^16 bytes)? If so, write "YES". If not, write "NO" and briefly explain why not.

c. Is it possible that the MMU used paging with page size 4 KB (2^12 bytes)? If so, write "YES". If not, write "NO" and briefly explain why not.

```json
{
  "problem_id": "4",
  "points": 8,
  "type": "Freeform",
  "tags": ["memory-management", "mmu", "virtual-memory"],
  "answer": "a) NO — the translations imply different relocation offsets for different addresses, so a single relocation register cannot explain them. b) NO — with 64 KB pages the low 16-bit offsets must match between virtual and physical addresses on the same page, but observed offsets differ. c) YES — 4 KB pages are consistent with the observed mappings (same 12-bit offsets where required).",
  "llm_judge_instructions": "Total 8 pts: Part a (3 pts) — award 3 pts for correctly answering NO with a brief correct justification that translations use different offsets. Part b (3 pts) — award 3 pts for correctly answering NO with a brief correct justification about 16-bit offsets. Part c (2 pts) — award 2 pts for correctly answering YES with brief justification. Partial credit allowed for partially correct explanations."
}
```

---

## Question 5 [10 point(s)]

Answer each part briefly and clearly.

5a. Is it possible for a thread’s kernel stack to contain more than one trapframe? If yes, write "YES" and identify a situation in which this could occur. If not, write "NO".

5b. Is it possible that a call to OS/161’s wchan_sleep function will cause a thread context switch? Answer "YES" or "NO" and briefly explain.

5c. Each page table entry normally includes a valid bit. Explain the purpose of the valid bit. What happens if a process attempts to access a virtual address on a page whose page table entry has the valid bit unset?

5d. When a system call occurs in OS/161, how does the kernel know which system call has been requested? Explain briefly.

```json
{
  "problem_id": "5",
  "points": 10,
  "type": "Freeform",
  "tags": ["os161", "kernel", "system-calls"],
  "answer": "a) YES — for example, if a thread is executing in the kernel (causing a trapframe) and an interrupt occurs, a second trapframe may be pushed; b) YES — wchan_sleep blocks the calling thread causing the scheduler to pick another thread to run (context switch); c) The valid bit indicates whether the mapping is present/usable; accessing a page with valid=0 causes a page fault/exception which the kernel must handle; d) The user program places a syscall code in a predefined register (e.g., v0/r2) before invoking the syscall; the kernel reads that register to determine which syscall was requested.",
  "llm_judge_instructions": "Total 10 pts: Part a (3 pts) — award 3 pts for correct YES/NO and a clear example if YES. Part b (2 pts) — award 2 pts for correct YES/NO and brief explanation. Part c (2 pts) — award 2 pts for correct explanation of valid bit and exception behavior. Part d (3 pts) — award 3 pts for stating that a syscall code is placed in a known register and the kernel inspects it; brief clarity required. Partial credit allowed per part."
}
```

---

## Question 6 [10 point(s)]

Answer each part briefly and clearly.

6a. List the different transitions between the three thread states (Ready, Running, Blocked). Why can’t a thread go from Blocked directly to Running?

6b. Explain the difference between a trapframe and a switchframe. What generates a trapframe? What generates a switchframe?

6c. Describe a scenario in which releasing a spinlock (spinlockrelease(&sem->semlock)) before acquiring the wchan lock (wchan_lock(sem->semwchan)) in the semaphore P() implementation can cause a concurrency problem. Explain briefly.

6d. What information can be found in each TLB entry?

```json
{
  "problem_id": "6",
  "points": 10,
  "type": "Freeform",
  "tags": ["os161", "thread-states", "tlb"],
  "answer": "a) Transitions: Ready -> Running (dispatch), Running -> Ready (preemption or yield), Running -> Blocked (sleep/wait), Blocked -> Ready (wake). A Blocked thread cannot go directly to Running because the scheduler must move it from Ready to Running. b) Trapframe stores processor state saved on an exception/interrupt/syscall; generated by the hardware/exception handling entry. Switchframe stores the minimal registers needed to resume a thread during context switch; generated by thread switch code (thread_yield/threadswitch). c) If the spinlock protecting the semaphore is released before taking the wait-channel lock, a V() may occur in between and wake a thread that hasn't yet gone to sleep, causing a missed wakeup and possible deadlock. d) TLB entries map virtual page numbers to physical frame numbers and typically include permission/valid bits and possibly ASID/flags.",
  "llm_judge_instructions": "Total 10 pts: Part a (3 pts) — 3 pts for listing transitions and correct explanation. Part b (2 pts) — 2 pts for distinguishing trapframe vs switchframe and identifying generators. Part c (3 pts) — 3 pts for a clear scenario explaining missed wakeup. Part d (2 pts) — 2 pts for listing page->frame mapping and common metadata (valid/permission)."
}
```

---

## Question 7 [12 point(s)]

You have been hired to design the matchmaking system for a multiplayer game. A match consists of 3 players and can start only when all 3 players are available. The company has one server that can host only one match at a time. A new match can start only when (a) the previous match has finished, and (b) three players are available.

Implement the following functions (you may define global variables). The functions are called as described:
- game_syncinit(): Called once before any players arrive.
- gamesynccleanup(): Called once when the system is taken down.
- before_match(): Called once by each player before that player starts a match. Should block until the player's match can start.
- after_match(): Called once for each player after that player's match finishes.

Provide a synchronization solution that enforces the constraints above.

```json
{
  "problem_id": "7",
  "points": 12,
  "type": "Freeform",
  "tags": ["synchronization", "multiparty-games", "threads"],
  "answer": "A correct solution initializes a lock and condition variable and uses counters to track waiting players, players in the current game, and players forming the next game. Example approach: game_syncinit initializes lock, cv, num_waiting=0, num_in_game=0, num_in_next=0; before_match acquires lock, increments num_waiting, then waits until num_waiting>=3 and num_in_game==0; forms the group by decrementing num_waiting by 3 and setting num_in_game=3, then releases lock; after_match acquires lock, decrements num_in_game; if num_in_game==0 and num_waiting>=3 then wake one waiter to begin next chaining; release lock; gamesynccleanup destroys lock and cv. Any equivalent correct implementation that ensures only one match runs at a time and matches start only when three players are available earns full credit.",
  "llm_judge_instructions": "Total 12 pts: Award 3 pts for correct initialization and cleanup. Award 5 pts for a correct before_match implementation that blocks appropriately, forms exact groups of 3, prevents starting when a game is in progress, and wakes players correctly. Award 4 pts for a correct after_match that decrements in-game count and wakes next players when appropriate. Partial credit allocated proportionally for partially correct synchronization logic; deduct credit for solutions that allow >1 concurrent game or that can deadlock/miss wakeups."
}
```

---

## End of Examination