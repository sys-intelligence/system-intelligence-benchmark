```json
{
  "exam_id": "cs350_spring_2013_midterm",
  "test_paper_name": "CS 350 Spring 2013 Midterm",
  "course": "CS 350",
  "institution": "University of Waterloo",
  "year": 2013,
  "score_total": 44,
  "num_questions": 20
}
```

# CS 350 Spring 2013 Midterm

---

## Question 1a [2 point(s)]

Explain why registers k0 & k1 cannot be used (even temporarily) by gcc in OS/161.

```json
{
  "problem_id": "1a",
  "points": 2,
  "type": "Freeform",
  "tags": ["os161", "trap-frames", "kernel"],
  "answer": "k0 & k1 are overwritten by the kernel's exception handler before the trap frame is stored; therefore compiler-generated code cannot safely use them across system traps.",
  "llm_judge_instructions": "2 points total: Award 2 points if the answer states that k0 and k1 are clobbered/overwritten by the kernel during exception handling (before the trap frame is saved), making them unsafe for compiler use. Award 1 point for a partially correct answer (e.g., mentions they are saved/restored by trap handling without explicitly stating they are overwritten). 0 points otherwise."
}
```

---

## Question 1b [1 point]

Explain why there are more registers stored in a trap frame than in a thread context.

```json
{
  "problem_id": "1b",
  "points": 1,
  "type": "Freeform",
  "tags": ["os161", "trap-frames", "contexts"],
  "answer": "Trap frames must save (almost) all registers because they are produced asynchronously by exceptions/interrupts; thread contexts save only the registers needed to resume a thread during a deliberate context switch.",
  "llm_judge_instructions": "1 point: Award 1 point if the answer explains that trap frames capture nearly all registers because exceptions are asynchronous, whereas thread context switches save only the necessary registers for a controlled switch. 0 points otherwise."
}
```

---

## Question 1c [1 point]

True or false: If there are no global variables, then no locks are necessary. Briefly justify your answer.

```json
{
  "problem_id": "1c",
  "points": 1,
  "type": "Freeform",
  "tags": ["concurrency", "locks"],
  "answer": "False. Locks protect shared resources beyond globals (e.g., heap memory, I/O devices, shared data structures).",
  "llm_judge_instructions": "1 point: Award 1 point if the answer states that locks may be needed for shared resources other than global variables (examples: heap, shared data structures, devices). 0 points otherwise."
}
```

---

## Question 1d [1 point]

Give one advantage and one disadvantage of having a software design with high lock granularity (many locks).

```json
{
  "problem_id": "1d",
  "points": 1,
  "type": "Freeform",
  "tags": ["synchronization", "locks"],
  "answer": "Advantage: increased concurrency (finer-grained locking). Disadvantage: higher overhead and greater risk of deadlock/complexity.",
  "llm_judge_instructions": "1 point: Award 1 point if the answer mentions an advantage (e.g., better concurrency) and a disadvantage (e.g., more overhead or higher deadlock/complexity risk). Award 0.5 if only one of advantage/disadvantage is given. 0 points if neither is correct."
}
```

---

## Question 1e [2 point(s)]

Briefly explain what this line of code is doing and why:

mips_syscall(struct trapframe *tf) { 
  ... 
  tf->tf_v0 = retval;       <---- explain this line 

```json
{
  "problem_id": "1e",
  "points": 2,
  "type": "Freeform",
  "tags": ["syscalls", "trapframe", "mips"],
  "answer": "This sets the syscall return value into the trapframe register v0 so that when control returns to the user process, the user-visible register v0 contains the return value of the system call.",
  "llm_judge_instructions": "2 points total: Award 2 points if the answer states that the line places the syscall return value into register v0 in the trap frame so the resumed user process sees the return value. Award 1 point for partial description (e.g., mentions return value propagation but not v0 or trapframe). 0 points otherwise."
}
```

---

## Question 1f [1 point]

Briefly describe why the C stdio library binary is not portable between different operating systems, even on the same hardware (machine architecture).

```json
{
  "problem_id": "1f",
  "points": 1,
  "type": "Freeform",
  "tags": ["portability", "osal", "abstraction"],
  "answer": "Binaries depend on OS-specific calling conventions and system call interfaces; different OSes use different syscall numbers/ABI and runtime conventions.",
  "llm_judge_instructions": "1 point: Award 1 point if the answer mentions OS-specific conventions for system calls or ABIs/ calling conventions that differ across OSes. 0 points otherwise."
}
```

---

## Question 1g [1 point]

Explain the primary difference (as discussed in class) between Hoare semantics and Mesa semantics used in OS/161. Then answer: A system uses a dynamic relocation virtual address scheme. The virtual addresses are 16 bits long, but the relocation register is 32 bits long. What is the maximum amount of physical memory that can be made available to each process? How much physical RAM can the entire system support?

```json
{
  "problem_id": "1g",
  "points": 1,
  "type": "Freeform",
  "tags": ["concurrency", "semantics", "memory-management"],
  "answer": "Hoare semantics: the signaling thread immediately transfers control to a waiting thread (the waiter runs immediately). Mesa semantics: signaling merely wakes a waiter, but the signaling thread continues; the waiter must reacquire the lock. With 16-bit virtual addresses, each process can address 2^16 = 64KB. With a 32-bit relocation register, the system can map up to 2^32 = 4GB of physical memory overall.",
  "llm_judge_instructions": "1 point total: Award 1 point if the answer correctly (a) distinguishes Hoare vs Mesa semantics (i.e., immediate transfer vs wake-only) and (b) states 64KB per-process limit and 4GB system RAM. Award 0.5 if only one of (a) or (b) is correct. 0 points otherwise."
}
```

---

## Question 1h [1 point]

What is the difference between internal and external memory fragmentation?

```json
{
  "problem_id": "1h",
  "points": 1,
  "type": "Freeform",
  "tags": ["memory-management", "fragmentation"],
  "answer": "Internal fragmentation is wasted space inside an allocated region (e.g., due to page granularity). External fragmentation is unusable free space between allocations when contiguous blocks are required.",
  "llm_judge_instructions": "1 point: Award 1 point if the answer correctly explains internal fragmentation (wasted space inside allocations due to fixed allocation unit) and external fragmentation (wasted small free blocks between allocations requiring contiguity). 0 points otherwise."
}
```

---

## Question 1i [1 point]

Explain why dumbvm is more like dynamic relocation than paging.

```json
{
  "problem_id": "1i",
  "points": 1,
  "type": "Freeform",
  "tags": ["virtual-memory", "dumbvm"],
  "answer": "dumbvm assigns contiguous physical memory regions per segment and stores a base (relocation) rather than per-page mappings; it requires segment contiguity similar to dynamic relocation.",
  "llm_judge_instructions": "1 point: Award 1 point if the answer states that dumbvm uses contiguous segments and a base relocation rather than page tables, noting absence of per-page mapping. 0 points otherwise."
}
```

---

## Question 1j [1 point]

Give one advantage and one disadvantage of having a small quantum.

```json
{
  "problem_id": "1j",
  "points": 1,
  "type": "Freeform",
  "tags": ["scheduling", "quantum"],
  "answer": "Advantage: improved responsiveness (lower latency). Disadvantage: higher scheduling overhead due to more context switches.",
  "llm_judge_instructions": "1 point: Award 1 point if the answer mentions both an advantage (e.g., responsiveness) and a disadvantage (e.g., context-switch overhead). Award 0.5 if only one is given. 0 points otherwise."
}
```

---

## Question 1k [1 point]

Explain the significance of the return value of fork().

```json
{
  "problem_id": "1k",
  "points": 1,
  "type": "Freeform",
  "tags": ["process-management", "fork"],
  "answer": "fork() returns 0 to the child and the child's PID to the parent, allowing each to determine its identity and take different execution paths.",
  "llm_judge_instructions": "1 point: Award 1 point if the answer states that fork() returns 0 in the child and the child's PID in the parent (allowing differentiation). 0 points otherwise."
}
```

---

## Question 2a [3 point(s)]

Given the following MIPS 64-bit TLB entry specification (with 4k page sizes)

VPAGE  bits  44-63 
PFRAME bits 12-31 
DIRTY  bit   10 
VALID  bit    9 

and the following TLB entries (in hex):

0x0000000000006600
0x0000100000002200
0x0012300045645600
0x0040000000400400
0x1000000010000600

For each virtual address below, give the corresponding physical address. If it cannot be determined or a fault would occur reading the address, write “FAULT”.

0x00000006
0x00006006
0x100000001
0x100000001
0x00123456
0x45645645
0x00001234
0x00400040
0x80123456

(Note: supply one mapping per listed virtual address.)

```json
{
  "problem_id": "2a",
  "points": 3,
  "type": "Freeform",
  "tags": ["memory-management", "tlb"],
  "answer": "Mappings depend on matching VPAGE to TLB entries and combining page offset with PFRAME. Expected answers should identify the correct physical addresses or FAULT for each virtual address.",
  "llm_judge_instructions": "3 points total: There are 7 addresses to map. Award (3/7) points per correct mapping (i.e., total points = correct_mappings * 3/7). For example, if 5 out of 7 mappings are correct, award 5*(3/7) points. Round fractional points to two decimal places if needed. 0 points for none correct."
}
```

---

## Question 2b [3 point(s)]

For each physical address, provide the corresponding virtual address. If it cannot be determined, write “UNKNOWN”.

0x00000006
0x100000001
0x45645645
0x00400040
0x80123456

```json
{
  "problem_id": "2b",
  "points": 3,
  "type": "Freeform",
  "tags": ["memory-management", "tlb"],
  "answer": "Determine possible virtual addresses that map to each physical address given the TLB entries; if multiple virtual pages could map to the same physical frame or no mapping exists, state UNKNOWN.",
  "llm_judge_instructions": "3 points total: There are 5 addresses. Award (3/5) points per correct identification (i.e., each correct mapping is worth 0.6 points). If the correct response is UNKNOWN, award full credit for that entry. Round fractional points to two decimal places if necessary."
}
```

---

## Question 3a [4 point(s)]

(a) Give a proof as to why resource ordering can prevent deadlocks. It can be informal but should be sound.

```json
{
  "problem_id": "3a",
  "points": 4,
  "type": "Freeform",
  "tags": ["deadlock-prevention", "resource-ordering"],
  "answer": "With a global total order on resources and the rule that each thread acquires resources in ascending order, any cycle in the resource-allocation graph would imply an impossible ordering contradiction (e.g., RN < R1 and R1 < RN). Hence cycles (and thus deadlocks) cannot occur.",
  "llm_judge_instructions": "4 points total: Award 2 points for clearly stating the core idea that a global ascending order on resource acquisition prevents cycles in the allocation graph. Award 2 more points for presenting a correct contradiction argument (e.g., assume a cycle exists and show it implies an impossible ordering relation). Partial credit distributed proportionally if the explanation captures the main idea but lacks rigour."
}
```

---

## Question 3b [4 point(s)]

(b) Here is Peterson’s algorithm as presented in class:

volatile boolean flag[2]; // initially false 
volatile int turn; 
// for thread A: i = 0 & j = 1, thread B: i = 1 & j = 0 
 
flag[i] = true; 
turn = j; 
while (flag[j] && turn == j) { } 
//critical section 
flag[i] = false; 

Your friend has implemented Peterson’s algorithm for OS/161 as follows (tid is 0 or 1):

turn = 1 - tid; 
flag[tid] = 1; 
while (turn != tid && flag[1 - tid]) { } 
//critical section 
flag[tid] = 0; 

Describe whether the critical section is protected in this implementation. Justify your answer.

```json
{
  "problem_id": "3b",
  "points": 4,
  "type": "Freeform",
  "tags": ["concurrency", "peterson"],
  "answer": "The implementation is incorrect; swapping the order of setting turn and flag (and/or using the inverted condition) breaks the intended mutual-exclusion protocol and can allow both threads to enter the critical section. A correct implementation must set flag[tid] = true before setting turn = other, and use the loop condition matching the canonical algorithm.",
  "llm_judge_instructions": "4 points total: Award 2 points for correctly identifying that the implementation does NOT guarantee mutual exclusion. Award 2 points for a clear explanation of why (e.g., incorrect ordering of setting turn and flag leads to a race where both threads may proceed). Partial credit: 1 point for identifying a symptom (e.g., 'ordering wrong' or 'might allow both in') without full justification."
}
```

---

## Question 4a [2 point(s)]

(a) Concisely explain how, in your A1 cat/mouse solution, the decision was made to switch from allowing one animal to eat (e.g., cats) to the other animal eating (e.g., mice). If you did not complete assignment 1, describe the naïve solution discussed in class.

```json
{
  "problem_id": "4a",
  "points": 2,
  "type": "Freeform",
  "tags": ["cat-mouse", "synchronization"],
  "answer": "Students should describe their chosen switching policy (e.g., count-based alternation, fairness queue, or the naïve solution of allowing one type until none remain).",
  "llm_judge_instructions": "2 points total: Award up to 2 points for a clear explanation of the switching decision. 1 point for a correct description of the naïve solution or partial description of a switching policy. 0 points for an unrelated answer."
}
```

---

## Question 4b [1 point]

(b) Given the above specifications and that (c >> b) and (m >> b), describe any circumstances under which your solution described in a) would achieve its maximum efficiency, and then calculate that efficiency as a formula using the variables c, m, b and t as necessary.

```json
{
  "problem_id": "4b",
  "points": 1,
  "type": "Freeform",
  "tags": ["performance", "efficiency", "synchronization"],
  "answer": "Maximum efficiency occurs when contention on bowls is minimized (e.g., when the number of bowls b >= number of concurrently hungry animals of the same type), yielding efficiency = 1 in the ideal single-bowler or non-contention case. Otherwise, efficiency depends on c, m, b, t per the chosen model.",
  "llm_judge_instructions": "1 point: Award 1 point for correctly identifying the trivial maximum-efficiency case (no contention, efficiency = 1) or for providing a correct formula/condition using c, m, b, t that gives maximum efficiency. 0 points otherwise."
}
```

---

## Question 4c [4 point(s)]

(c) Given the above specifications, consider the following solution: “Allow k mice to eat, then allow k cats to eat, and then allow k mice to eat, and so on...”

Determine the efficiency for each scenario below. For each scenario, give the maximum wait time for both cats and mice. The wait time is the amount of time that elapses from when cat X finishes eating, until cat X starts to eat again. Assume fairness amongst animals of the same type: once cat X eats, all other cats will eat exactly once before cat X eats again.

Provide answers for the scenarios listed in the exam (use the provided b, c, m, t, k values).

```json
{
  "problem_id": "4c",
  "points": 4,
  "type": "Freeform",
  "tags": ["cat-mouse", "scheduling", "efficiency"],
  "answer": "Compute efficiency = useful eating time / total time in the alternating-k schedule; compute max wait time for cats and mice based on number of animals, k, bowls b, and per-eating time t.",
  "llm_judge_instructions": "4 points total: Award 2 points for correct efficiency calculations across the scenarios (pro-rated if not all scenarios correct). Award 1 point for correct maximum wait time for cats across scenarios (pro-rated). Award 1 point for correct maximum wait time for mice across scenarios (pro-rated). If partial scenarios are correct, distribute points proportionally."
}
```

---

## Question 5 [9 point(s)]

For this problem, you are required to use semaphores to simulate a school cafeteria. 
- There are an arbitrary number of students. Each student is a separate thread. 
- There is no coordinating thread; there are K stations in the cafeteria, numbered 0..K-1 (where K is a global constant). 
- Only one student can occupy a station at a time. 
- Students must start at station 0 and finish at station K-1, in their original ordering. 
- There may be more students than stations, so you must maintain a queue of students waiting to get to the first station. 
- The following unsynchronized list functions are provided: is_empty(), list_peek_front(), list_remove_front(), list_append(struct student *s). 
- Each student may need more than one food item at a station. The number of items student s needs to acquire at station i is s->items[i], which could be zero. 
- For each item at station i the student must call: get_item(struct student *s, int i); When the function returns, the student will have the item, but it may block during the function call to wait for the food. 
- You must ensure that get_item is synchronized and is never called more than once at the same time for either the same student s or the same station i. 
- You may use thread_sleep and thread_wakeup if you wish. 
List your global variables and semaphores here. Indicate the initial value of each variable & semaphore.

```json
{
  "problem_id": "5",
  "points": 9,
  "type": "Freeform",
  "tags": ["semaphores", "synchronization", "cafeteria"],
  "answer": "A correct solution lists global semaphores/variables (e.g., queue lock, queue data structure, per-station semaphores for mutual exclusion, per-station get_item locks), their initial values, and describes how students wait in queue, advance station-by-station preserving ordering, and call get_item with both student-and-station mutual exclusion. For example: semaphore queue_lock = 1; queue list initially empty; semaphore station_mutex[K] = 1 for each station; semaphore get_item_mutex[K] = 1 for each station; additional per-student lock if required. Detailed pseudocode should show enqueue/dequeue and the protocol to move between stations.",
  "llm_judge_instructions": "9 points total: Award up to 3 points for correct and complete listing of global variables and semaphores with proper initial values. Award up to 3 points for correct queue and ordering logic ensuring students start at station 0 and preserve original ordering. Award up to 3 points for correct synchronization of get_item so that it is never called concurrently for the same student or same station (e.g., appropriate use of per-station and per-student locks or semaphores). Partial credit as appropriate."
}
```

---

## Bonus Question [1 point]

Please answer the following 3 Likert-style questions honestly at the end of the exam:

1) This exam was too long: a) Strongly disagree b) Disagree c) Neutral d) Agree e) Strongly agree  
2) This exam was too hard: a) Strongly disagree b) Disagree c) Neutral d) Agree e) Strongly agree  
3) This exam was fair: a) Strongly disagree b) Disagree c) Neutral d) Agree e) Strongly agree

Also: Draw a picture that illustrates a thread switching from user mode to privileged (kernel) mode. Humorous illustrations encouraged.

```json
{
  "problem_id": "bonus",
  "points": 1,
  "type": "Freeform",
  "tags": ["bonus"],
  "answer": "",
  "llm_judge_instructions": "1 point: Award 1 point for an attempted response to the three Likert items and either a drawing or a brief description of a drawing that shows a thread switching from user to kernel mode. 0 points if nothing is attempted."
}
```