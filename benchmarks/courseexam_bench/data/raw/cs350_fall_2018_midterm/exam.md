# CS350 Fall 2018 Midterm

```json
{
  "exam_id": "cs350_fall_2018_midterm",
  "test_paper_name": "CS350 Fall 2018 Midterm",
  "course": "CS350",
  "institution": "University of Waterloo",
  "year": 2018,
  "score_total": 57,
  "num_questions": 18
}
```

---

## Question 1 [2 point(s)]

Is it possible to have more than one switchframe in a kernel stack?  Explain why or why not.

```json
{
  "problem_id": "1",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-stack","os"],
  "answer": "No. There can only be one switchframe in a kernel stack.",
  "llm_judge_instructions": "Award 2 points for a correct explanation that there can only be one switchframe in a kernel stack and that a switchframe is popped on return. Award 0 points otherwise."
}
```

---

## Question 2 [3 point(s)]

Explain  why  the  following  implementation  of  semaphore  P  is  incorrect.   Provide  an  example interaction between two threads that illustrates the problem.

```json
{
  "problem_id": "2",
  "points": 3,
  "type": "Freeform",
  "tags": ["semaphore","concurrency"],
  "answer": "wchanlock should be called before spinlockrelease. In this incorrect implementation, there is a small window in which no locks are held. During this window, the semaphore state can be changed by another thread.",
  "llm_judge_instructions": "Award 2 points for identifying the bug: that the wait-channel lock (wchanlock) must be acquired before releasing the spinlock. Award 1 point for providing an example interleaving between two threads that demonstrates the window where the semaphore state can be changed. 0 points otherwise."
}
```

---

## Question 3 [2 point(s)]

Explain why system calls need to increment the EPC by 4 before returning to user space.  Why is incrementing the EPC not necessary when handling other exceptions?

```json
{
  "problem_id": "3",
  "points": 2,
  "type": "Freeform",
  "tags": ["system-call","exception"],
  "answer": "The syscall instruction is the cause of the exception; if EPC is not advanced past the syscall instruction, returning to user space will re-execute the syscall and cause the exception again. For other exceptions, the cause is typically a transient condition and the instruction can be retried without re-triggering the same exception.",
  "llm_judge_instructions": "Award 2 points for stating that EPC must be advanced to avoid re-executing the syscall instruction and thus retriggering the syscall exception. Award 1 point for a partial explanation that mentions advancing EPC or resuming after handling but does not explicitly link it to retriggering the syscall. Award 0 points otherwise."
}
```

---

## Question 4 [2 point(s)]

Explain why a page table entry does not contain a page number, yet a TLB entry contains both a page number and a frame number.

```json
{
  "problem_id": "4",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging","tlb"],
  "answer": "The page number is the index into the page table array, so it would be redundant to store it in the PTE. The TLB is a cache and must store tags (the page number) along with the frame number to indicate which virtual page each cached entry corresponds to.",
  "llm_judge_instructions": "Award 2 points for recognizing that the PTE's index is the page number (so storing it in the PTE is redundant) and that the TLB stores page-number tags because it is a cache. Award 0 points otherwise."
}
```

---

## Question 5 [2 point(s)]

A trapframe contains more information than a switchframe.  Why?

```json
{
  "problem_id": "5",
  "points": 2,
  "type": "Freeform",
  "tags": ["trapframe","stack-frame"],
  "answer": "A trapframe is used to save the full processor context when an exception or interrupt occurs (no calling conventions can be assumed), whereas a switchframe follows function calling conventions and may omit saving caller-saved registers.",
  "llm_judge_instructions": "Award 2 points for noting that trapframes preserve the full processor context for exceptions while switchframes rely on function calling conventions and may not preserve all registers. Award 0 points otherwise."
}
```

---

## Question 6 [4 point(s)]

Imagine a version of OS/161 with the following bug:  When the exception caused by division by zero is raised, the kernel instead handles it as a system call.  What will be the behavior of the following program if the compiler stores n in v0 and d in a0?  What will be the behavior if the compiler stores n in a0 and d in v0?
Table of system calls:
System CallSystem Call #
pid_t fork(void) 0
pid_t vfork(void) 1
int execv(const char *program, char **args) 2
void exit(int exitcode) 3
pid_t waitpid(pid_t, int *status, int options) 4
pid_t getpid(void) 5

int main() {
  int n = 6;
  int d;
  for (d = 2; d >= 0; d--)
    n /= d;
  printf("%d\n", d);
  return 0;
}

```json
{
  "problem_id": "6",
  "points": 4,
  "type": "Freeform",
  "tags": ["system-calls","c-programming"],
  "answer": "If the compiler places n in v0 and d in a0, the division-by-zero exception being mis-handled as a syscall will likely be treated as an exit(0) (or other system call depending on calling convention and syscall number), causing the program to exit with code 0. If the compiler places n in a0 and d in v0, the mis-handled exception may be treated as fork/vfork or another syscall that spawns child processes, resulting in children being spawned in a loop; these children may observe different register setups (e.g., printing -1) depending on the exact misinterpreted syscall behavior.",
  "llm_judge_instructions": "Award 4 points for correctly identifying both behaviors: (a) the case that results in program exit with exit code 0, and (b) the case that results in spawning children (approximate description of children behavior). If only one case is correct, award 2 points. Award 0 points otherwise."
}
```

---

## Question 7 [2 point(s)]

What concurrency problem does this program suffer from?

```json
{
  "problem_id": "7",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency","deadlock"],
  "answer": "Deadlock",
  "llm_judge_instructions": "Award 2 points for identifying deadlock. Award 0 points otherwise."
}
```

---

## Question 8 [4 point(s)]

Provide a sequence of events that can trigger this problem.

```json
{
  "problem_id": "8",
  "points": 4,
  "type": "Freeform",
  "tags": ["concurrency","deadlock"],
  "answer": "One possible sequence: Thread 1 calls funcAB and goes to sleep in cv_wait holding lock A; Thread 2 calls funcB and acquires lock B; Thread 3 calls funcAB and acquires lock B and then tries to acquire lock A and blocks; Thread 1 wakes and tries to acquire lock B and blocks — circular waiting results in deadlock.",
  "llm_judge_instructions": "Award 4 points for a correct interleaving that clearly leads to deadlock. Award 2 points for a mostly correct sequence missing one key step or lock detail. Award 1 point for a minimal description that identifies conflicting locks but lacks a full interleaving. Award 0 points otherwise."
}
```

---

## Question 9 [2 point(s)]

What changes to any of the above functions would address this problem?

```json
{
  "problem_id": "9",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency","deadlock"],
  "answer": "Use a consistent lock ordering (always acquire lock A before lock B) or otherwise ensure locks are acquired in a global order to prevent circular waiting.",
  "llm_judge_instructions": "Award 2 points for correctly identifying the fix (e.g., consistent global lock ordering). Award 0 points otherwise."
}
```

---

## Question 10 [2 point(s)]

In a single-level paged system, how many bits of a virtual memory address would refer to the page number and how many to the offset?  How many bits of a physical address would refer to the frame number and how many to the offset?

```json
{
  "problem_id": "10",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging","memory-management"],
  "answer": "Virtual address: 20 bits page number, 12 bits offset. Physical address: 36 bits frame number, 12 bits offset.",
  "llm_judge_instructions": "Award 2 points for correctly identifying virtual page-number and offset bits and physical frame-number and offset bits as stated. Award 0 points otherwise."
}
```

---

## Question 11 [2 point(s)]

How many bytes would a single-level page table require?

```json
{
  "problem_id": "11",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging","memory-management"],
  "answer": "2^23 bytes",
  "llm_judge_instructions": "Award 2 points for correctly reporting 2^23 bytes. Award 0 points otherwise."
}
```

---

## Question 12 [2 point(s)]

If a page table entry contains a frame number, a valid bit, a writeable bit, and a single bit for tracking page usage, how many bits per page table entry are unused?

```json
{
  "problem_id": "12",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging","pte"],
  "answer": "25",
  "llm_judge_instructions": "Compute 64 - 36 - 3 = 25 and award 2 points for the correct calculation. Award 0 points otherwise."
}
```

---

## Question 13 [2 point(s)]

How many page table entries fit onto a single page?

```json
{
  "problem_id": "13",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging","memory-management"],
  "answer": "512",
  "llm_judge_instructions": "Award 2 points for correct calculation 2^9 = 512. Award 0 points otherwise."
}
```

---

## Question 14 [2 point(s)]

What is the minimum number of levels necessary to implement a multi-level paged system if each page table at each level must fit into a single page?

```json
{
  "problem_id": "14",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging","multilevel"],
  "answer": "3",
  "llm_judge_instructions": "Award 2 points for answering 3 levels. Award 0 points otherwise."
}
```

---

## Question 15 [3 point(s)]

Change the following sketch of an implementation of fork to instead implement vfork.  Assume that the appropriate changes are made to execv elsewhere.  You may cross out steps and add new steps.

sys_fork() {
create process structure
copy address space
choose pid for new process
create parent/child relationship
duplicate trapframe
create thread for new process (running child_process)
}
child_process() {
copy trapframe to stack
modify trapframe
enter usermode
}
Replace “copy address space” with “link to same address space”, and add “block until child has reached execv”.

```json
{
  "problem_id": "15",
  "points": 3,
  "type": "Freeform",
  "tags": ["vfork","os-161"],
  "answer": "Replace 'copy address space' with linking to the parent's address space and add a mechanism to block the parent until the child calls execv or exits.",
  "llm_judge_instructions": "Award 3 points for correctly describing replacing address-space copying with linking to the same address space and adding parent blocking until the child reaches execv. Award 0 points otherwise."
}
```

---

## Question 16 [3 point(s)]

Each change in the semantics of vfork impacts the implementation of execv.   How would an implementation of execv need to differ to support both of these changes in vfork?

```json
{
  "problem_id": "16",
  "points": 3,
  "type": "Freeform",
  "tags": ["vfork","execv"],
  "answer": "If the process was created with vfork, execv must not immediately destroy the shared address space; instead it should replace the address space for the child and signal/unblock the parent when the child has completed execv (or on error).",
  "llm_judge_instructions": "Award 3 points for correctly stating the need to preserve or atomically replace the address space for a vfork child and to signal/unblock the parent when execv has completed. Award 0 points otherwise."
}
```

---

## Question 17 [2 point(s)]

The documentation for vfork states that the child process shouldn’t return from the function that called vfork.  Why not?

```json
{
  "problem_id": "17",
  "points": 2,
  "type": "Freeform",
  "tags": ["vfork","stack"],
  "answer": "Because the child and parent share the userspace stack after vfork, if the child returns from the function that called vfork it will pop stack frames that the parent expects to still be present, leading to undefined behavior.",
  "llm_judge_instructions": "Award 2 points for recognizing that vfork shares the userspace stack and that returning would corrupt the stack expected by the parent. Award 0 points otherwise."
}
```

---

## Question 18 [16 point(s)]

You have been hired by the city of Waterloo to help solve a modified version of the “traffic intersection” problem for an intersection with significant pedestrian traffic. For safety, instead of allowing vehicles to share the intersection with pedestrians, you are to build a scramble intersection that, under specific conditions, stops vehicular traffic from all directions to allow pedestrians to cross the intersection.

Requirements (student sees):
- Pedestrians and vehicles must never be inside the intersection at the same time.
- Vehicles must not collide with other vehicles.
- When a pedestrian arrives, they must wait until the intersection is clear of vehicles before entering.
- No additional vehicles may enter while a pedestrian is waiting or inside.
- Two one-way roads: north-to-south and east-to-west. Vehicles originate from north or east and exit opposite direction; no turns.
- Implement the six synchronization functions: intersection_sync_init, intersection_sync_cleanup, intersection_before_vehicle_entry, intersection_after_vehicle_exit, intersection_before_pedestrian_entry, intersection_after_pedestrian_exit.
- Global variables may be defined. Solution should prioritize pedestrians while providing fairness between vehicle directions.

(Do NOT include any solution code in the question body; implementors will write the functions.)

```json
{
  "problem_id": "18",
  "points": 16,
  "type": "Freeform",
  "tags": ["synchronization","concurrency","traffic-intersection","pedestrians"],
  "answer": "Expected solution outline: Define a global lock, two direction condition variables (one per vehicle direction), a pedestrian condition variable, counters cars_inside[2] and cars_waiting[2], and ped_inside and ped_waiting, plus a next_after_ped variable to choose which vehicle direction is next. Implement intersection_sync_init to create the lock and condition variables and zero counters. Implement intersection_sync_cleanup to destroy condition variables and the lock. Implement intersection_before_vehicle_entry to acquire the lock, increment cars_waiting[origin], wait if pedestrians are inside or waiting or opposing cars are inside, then decrement cars_waiting and increment cars_inside and release the lock. Implement intersection_after_vehicle_exit to decrement cars_inside[origin]; if zero and pedestrians are waiting, wake pedestrians; otherwise wake the opposing vehicle direction and set next_after_ped appropriately. Implement intersection_before_pedestrian_entry to acquire the lock, increment ped_waiting, wait until no cars are inside, then decrement ped_waiting, increment ped_inside and release the lock. Implement intersection_after_pedestrian_exit to decrement ped_inside; if ped_inside becomes 0 then wake cars according to next_after_ped (broadcast the condition variable for that direction) or the opposing direction if none waiting. The solution must ensure mutual exclusion between vehicles and pedestrians and avoid starvation by appropriate wake ordering.",
  "llm_judge_instructions": "Award points as follows (total 16): 3 points for correct global variables and initialization (correct lock and CV creation and zeroing counters); 2 points for correct cleanup (destroying CVs and lock); 3 points for correct intersection_before_vehicle_entry (proper waiting conditions, cars_waiting handling, and cars_inside increment); 3 points for correct intersection_after_vehicle_exit (decrement, waking pedestrians or vehicles appropriately, and managing next_after_ped); 2 points for correct intersection_before_pedestrian_entry (waiting until no cars inside and handling ped counters); 3 points for correct intersection_after_pedestrian_exit (decrementing ped_inside, waking the correct vehicle direction based on next_after_ped). Award partial credit within each component when behavior is mostly correct but missing a detail; award 0 points for a component with incorrect synchronization that violates safety. Total must sum to 16."
}
```

---