# CS350 Midterm Spring 2013

```json
{
  "exam_id": "cs350_spring_2013_midterm",
  "test_paper_name": "CS350 Midterm Spring 2013",
  "course": "CS350",
  "institution": "University of Waterloo",
  "year": 2013,
  "score_total": 52,
  "num_questions": 19
}
```

---

## Question 1a [2 point(s)]

Explain why registers k0 & k1 cannot be used (even temporarily) by gcc in OS/161.

```json
{
  "problem_id": "1a",
  "points": 2,
  "type": "Freeform",
  "tags": ["os-161"],
  "answer": "k0 & k1 are overwritten by the kernel by the exception (interrupt) handler before the trap frame is stored.",
  "llm_judge_instructions": "Award 2 points for identifying that k0 and k1 are clobbered by the kernel during exception handling before the trap frame is saved; 0 points otherwise."
}
```

---

## Question 1b [2 point(s)]

Explain why there are more registers stored in a trap frame than in a thread context.

```json
{
  "problem_id": "1b",
  "points": 2,
  "type": "Freeform",
  "tags": ["os-161", "concurrency"],
  "answer": "Trap frames happen unexpectedly and must store (almost) all registers. Thread contexts occur purposefully and within functions (“subroutines”), so temp registers that are not preserved by subroutines do not have to be stored.",
  "llm_judge_instructions": "Award 2 points for mentioning that trap frames capture a broad set of registers due to asynchronous events, while thread contexts preserve a smaller set needed for function calls; 0 points otherwise."
}
```

---

## Question 1c [1 point(s)]

True or false: If there are no global variables, then no locks are necessary. Briefly justify your answer.

```json
{
  "problem_id": "1c",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["concurrency"],
  "choices": ["True", "False"],
  "answer": "B",
  "llm_judge_instructions": "Award 1 point for selecting 'False' and a brief justification that local variables may still be shared via pointers or other shared resources requiring synchronization; 0 points otherwise."
}
```

---

## Question 1d [1 point(s)]

Give one advantage and one disadvantage of having a software design with high lock granularity (many locks).

```json
{
  "problem_id": "1d",
  "points": 1,
  "type": "Freeform",
  "tags": ["concurrency"],
  "answer": "Advantage: better concurrency. Disadvantage: more overhead, greater chance of deadlock.",
  "llm_judge_instructions": "Award 1 point for identifying both an advantage (better concurrency) and a disadvantage (more overhead or higher deadlock risk). 0 points otherwise."
}
```

---

## Question 1e [2 point(s)]

Briefly explain what this line of code is doing and why:

mips_syscall(struct trapframe *tf) { 
  ... 
  tf->tf_v0 = retval;       // explain this line
}

```json
{
  "problem_id": "1e",
  "points": 2,
  "type": "Freeform",
  "tags": ["os-161"],
  "answer": "This modifies the trap frame so when the user process resumes it can access the return value of the system call (in register v0).",
  "llm_judge_instructions": "Award 2 points for a correct explanation that the line stores the system call return value into the user-visible trapframe register v0, enabling the process to observe the return value. 0 points otherwise."
}
```

---

## Question 1f [2 point(s)]

Briefly describe why the C stdio library binary is not portable between different operating systems, even on the same hardware (machine architecture).

```json
{
  "problem_id": "1f",
  "points": 2,
  "type": "Freeform",
  "tags": ["portability", "c-libraries"],
  "answer": "Each OS has its own conventions for enumerating system calls (and using registers).",
  "llm_judge_instructions": "Award 2 points for explaining that system call conventions and register usage differ across OSes, hindering portability. 0 points otherwise."
}
```

---

## Question 1g [2 point(s)]

Explain the primary difference (as discussed in class) between Hoare semantics and the Mesa semantics used in OS/161. A system uses a dynamic relocation virtual address scheme. The virtual addresses are 16 bits long, but the relocation register is 32 bits long. What is the maximum amount of physical memory that can be made available to each process? How much physical RAM can the entire system support?

```json
{
  "problem_id": "1g",
  "points": 2,
  "type": "Freeform",
  "tags": ["memory-management"],
  "answer": "Hoare semantics: signaling releases the lock immediately; Mesa semantics: signaling does not release the lock until requested. Maximum per-process memory: 64KB. System RAM: 4GB.",
  "llm_judge_instructions": "Award 2 points for correctly contrasting Hoare vs Mesa semantics and giving the numbers 64KB per process and 4GB system RAM. 0 points otherwise."
}
```

---

## Question 1h [1 point(s)]

What is the difference between internal and external memory fragmentation.

```json
{
  "problem_id": "1h",
  "points": 1,
  "type": "Freeform",
  "tags": ["memory-fragmentation"],
  "answer": "Internal: wasted space inside allocated blocks (e.g., paging). External: wasted space between allocated blocks (e.g., dynamic relocation).",
  "llm_judge_instructions": "Award 1 point for correctly distinguishing internal (within allocated units) vs external (between allocations) fragmentation. 0 points otherwise."
}
```

---

## Question 1i [1 point(s)]

Explain why dumbvm is more like dynamic relocation than paging.

```json
{
  "problem_id": "1i",
  "points": 1,
  "type": "Freeform",
  "tags": ["memory-management", "dumbvm"],
  "answer": "Like dynamic relocation, dumbvm requires its segments to be contiguous in memory – for each segment it only stores the starting location in physical memory (not a page table).",
  "llm_judge_instructions": "Award 1 point for identifying the contiguity of segments and lack of page tables as the reason it resembles dynamic relocation. 0 points otherwise."
}
```

---

## Question 1j [1 point(s)]

Give one advantage and one disadvantage of having a small quantum.

```json
{
  "problem_id": "1j",
  "points": 1,
  "type": "Freeform",
  "tags": ["scheduling"],
  "answer": "Advantage: OS is more responsive. Disadvantage: more overhead due to context switching.",
  "llm_judge_instructions": "Award 1 point for identifying both an advantage and a disadvantage. 0 points otherwise."
}
```

---

## Question 1k [1 point(s)]

Explain the significance of the return value of fork().

```json
{
  "problem_id": "1k",
  "points": 1,
  "type": "Freeform",
  "tags": ["process-management"],
  "answer": "The return value allows each process to determine if it is the parent (return value is child pid) or the child (return value is 0).",
  "llm_judge_instructions": "Award 1 point for recognizing that fork() returns different values in parent vs child to distinguish processes. 0 points otherwise."
}
```

---

## Question 2a [7 point(s)]

For each virtual address below, give the corresponding physical address. If it cannot be determined or a fault would occur reading the address, write “FAULT”.

0x0000 0006
0x1000 0001
0x0012 3456
0x4564 5645
0x0000 1234
0x0040 0040
0x8012 3456

```json
{
  "problem_id": "2a",
  "points": 7,
  "type": "Freeform",
  "tags": ["tlb", "memory-management"],
  "answer": "0x0000 0006 -> 0x0000 6006; 0x1000 0001 -> 0x1000 0001; 0x0012 3456 -> 0x4564 5456; 0x4564 5645 -> FAULT; 0x0000 1234 -> 0x0000 2234; 0x0040 0040 -> FAULT; 0x8012 3456 -> 0x0012 3456",
  "llm_judge_instructions": "Award 7 points total: award 1 point for each correctly determined physical address (or correctly writing 'FAULT') corresponding to the seven virtual addresses listed, in order; 0 points for each incorrect mapping."
}
```

---

## Question 2b [5 point(s)]

For each physical address, provide the corresponding virtual address. If it cannot be determined, write “UNKNOWN”.

0x0000 0006
0x1000 0001
0x4564 5645
0x0040 0040
0x8012 3456

```json
{
  "problem_id": "2b",
  "points": 5,
  "type": "Freeform",
  "tags": ["tlb", "memory-management"],
  "answer": "0x0000 0006 -> UNKNOWN; 0x1000 0001 -> 0x1000 0001; 0x4564 5645 -> 0x0012 3645; 0x0040 0040 -> UNKNOWN; 0x8012 3456 -> UNKNOWN",
  "llm_judge_instructions": "Award 5 points total: award 1 point for each correctly determined virtual address (or correctly writing 'UNKNOWN') corresponding to the five physical addresses listed, in order; 0 points for each incorrect mapping."
}
```

---

## Question 3a [4 point(s)]

Give a proof as to why resource ordering can prevent deadlocks. It can be informal, but it should be sound. You are not required to reference the deadlock detection algorithm, but you may reference it if you choose.

Aside: resource ordering requires a total order (ie: positive integers) which requires that each resource must have a unique value, and there can be no “duplicates”. In the problems we study with duplicate resources, they can be simply enumerated as separate resources.

```json
{
  "problem_id": "3a",
  "points": 4,
  "type": "Freeform",
  "tags": ["deadlock", "resource-ordering"],
  "answer": "A contradiction-based proof: if all threads acquire resources in strictly increasing order (per a total ordering of resources), then any cycle in the allocation graph would imply R1 < R2 < ... < Rn < R1, which is impossible. Therefore no cycle (deadlock) can occur.",
  "llm_judge_instructions": "Award 4 points for a sound contradiction-based argument that resource ordering prevents cycles in the allocation graph, hence prevents deadlocks. Specifically: 2 points for establishing that threads acquire resources in increasing order, 2 points for showing that a cycle would imply an impossible ordering (R1 < R1). 0 points otherwise."
}
```

---

## Question 3b [4 point(s)]

Here is Peterson’s algorithm as presented in class:  
volatile boolean flag[2]; // initially false  
volatile int turn;  
// for thread A: i = 0 & j = 1, thread B: i = 1 & j = 0  

flag[i] = true; 
turn = j; 
while (flag[j] && turn == j) { } 
//critical section 
flag[i] = false; 

Your friend has implemented Peterson’s algorithm for OS/161 as follows:  
(He used a thread id tid to identify each thread: tid has the value of either 0 or 1)

turn = 1 - tid; 
flag[tid] = 1; 
while (turn != tid && flag[1 - tid]) { } 
//critical section 
flag[tid] = 0; 

Describe how the critical section is protected (or not protected) in this implementation. Justify your answer.

```json
{
  "problem_id": "3b",
  "points": 4,
  "type": "Freeform",
  "tags": ["concurrency", "synchronization"],
  "answer": "The implementation is incorrect and does not guarantee mutual exclusion. The assignment of turn before setting flag allows both threads to observe conditions that let them both enter the critical section concurrently. The correct ordering must set flag[tid] before writing turn.",
  "llm_judge_instructions": "Award 4 points if the answer identifies that the implementation fails to provide mutual exclusion due to incorrect ordering (turn set before flag) and justifies with a concise execution interleaving showing both threads entering the critical section; partial credit (2 points) for stating the bug without a clear justification."
}
```

---

## Question 4a [2 point(s)]

Concisely explain how in your A1 cat/mouse solution the decision was made to switch from allowing one animal to eat (ie: cats) to the other animal eating (ie: mice). If you did not complete assignment 1, describe the naïve solution discussed in class.

(depends on assignment implementation)

```json
{
  "problem_id": "4a",
  "points": 2,
  "type": "Freeform",
  "tags": ["cat-mouse", "synchronization"],
  "answer": "(depends on assignment implementation)",
  "llm_judge_instructions": "Award 2 points if the answer mentions the decision mechanism (as implemented in the assignment) or the naïve solution discussed in class; 0 points otherwise."
}
```

---

## Question 4b [1 point(s)]

Given the above specifications and that (c >> b) and (m >> b), describe any circumstances under which your solution described in a) would achieve its maximum efficiency, and then calculate that efficiency as a formula using the variables c, m, b and t as necessary. Trivial solution: MOST solutions would achieve maximum efficiency (1) when there is only one bowl.

```json
{
  "problem_id": "4b",
  "points": 1,
  "type": "Freeform",
  "tags": ["scheduling", "concurrency"],
  "answer": "MOST solutions would achieve maximum efficiency (1) when there is only one bowl.",
  "llm_judge_instructions": "Award 1 point for identifying that maximum efficiency occurs when b = 1, and providing the formula 1 under those conditions. 0 points otherwise."
}
```

---

## Question 4c [4 point(s)]

Given the above specifications, consider the following solution:

“Allow k mice to eat, then allow k cats to eat, and then allow k mice to eat, and so on...”

Determine the efficiency for each scenario below. For each scenario, give the maximum wait time for both cats and mice. The wait time is the amount of time that elapses from when cat X finishes eating, and then cat X starts to eat again. Assume fairness amongst the animals of the same type: once cat X eats, all other cats will eat exactly once before cat X eats again.

Provide answers for the listed scenarios.

```json
{
  "problem_id": "4c",
  "points": 4,
  "type": "Freeform",
  "tags": ["cat-mouse", "synchronization"],
  "answer": "Compute efficiencies and maximum wait times per scenario using the parameters c, m, t, k: efficiency = (useful eating time) / (total time including switching overhead); maximum wait time for cats and mice follows from the ordering of k groups and the number of animals of each type. (Instructor solution provides numeric results for each scenario.)",
  "llm_judge_instructions": "Award up to 4 points for correctly computing the maximum wait times and efficiencies per the scenarios: 2 points for correct efficiency calculations across scenarios, and 2 points for correct maximum-wait calculations. Partial credit allowed per correct sub-results."
}
```

---

## Question 5 [9 point(s)]

For this problem, you are required to use semaphores to simulate a school cafeteria. 
- There are an arbitrary number of students. Each student is a separate thread. 
- There is no coordinating or dispatching thread. 
- There are K stations in the cafeteria, numbered 0..K-1 (where K is a global constant) 
- Only one student can occupy a station at a time. 
- Students must start at station 0 and finish at station K-1 in order, without skipping stations. 
- There may be more students than stations, so you must maintain a queue of students waiting to get to the first station. 
- The following unsynchronized list functions are provided: int is_empty(); struct student *list_peek_front(); struct student *list_remove_front(); void list_append(struct student *s);
- Each student may need more than one item at a station. The number of items student s needs to acquire at station i is s->items[i], which could be zero.
- For each item at station i the student must call: get_item(struct student *s, int i);
  When the function returns, the student will have the item, but it may block during the function call to wait for the food.
- You must ensure that get_item is synchronized and is never called more than once at the same time for either the same student s or the same station i.
- You may use thread_sleep and thread_wakeup if you wish.
List your global variables and semaphores here. Indicate the initial value of each variable & semaphore.

```json
{
  "problem_id": "5",
  "points": 9,
  "type": "Freeform",
  "tags": ["semaphores", "cs350", "cafeteria"],
  "answer": "",
  "llm_judge_instructions": "Award 9 points total: 3 points for correct declaration and initialization of global semaphores/locks (including queue lock and per-station locks) with initial values; 4 points for correct synchronization ensuring get_item is not called concurrently for the same student or same station (e.g., per-student and per-station locking protocol); 2 points for correct queue handling so students wait and are woken in FIFO order. Partial credit allowed per correct components."
}
```

---

## Bonus

This section is intentionally omitted from the exam text used to generate the questions.