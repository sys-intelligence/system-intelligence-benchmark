# CS530 Fall 2018 Midterm

```json
{
  "exam_id": "cs530_fall_2018_midterm",
  "test_paper_name": "CS530 Fall 2018 Midterm",
  "course": "CS530",
  "institution": "University of Waterloo",
  "year": 2018,
  "score_total": 57,
  "num_questions": 18
}
```

---

## Question 1a [2 point(s)]

Is it possible to have more than one switchframe in a kernel stack? Explain why or why not.

```json
{
  "problem_id": "1a",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "kernel"],
  "answer": "No. A running thread stores a switchframe in its kernel stack as it context switches to a different thread. Upon returning to the thread, the switchframe is popped off the thread’s kernel stack. Since it is not possible for a thread to context switch away twice without context switching back once in between, there can only be one switchframe in a kernel stack.",
  "llm_judge_instructions": "Award 2 points for stating that there can be at most one switchframe in a kernel stack and providing brief justification that a thread cannot context switch away twice without an intervening return; 0 points otherwise."
}
```

---

## Question 1b [3 point(s)]

Explain why the following implementation of semaphore P is incorrect. Provide an example interaction between two threads that illustrates the problem.

```c
void P(struct semaphore* sem) {
    spinlock_acquire(&sem->sem_lock);
    while (sem->sem_count == 0) {
        spinlock_release(&sem->sem_lock);
        wchan_lock(sem->sem_wchan);
        wchan_sleep(sem->sem_wchan);
        spinlock_acquire(&sem->sem_lock);
    }
    sem->sem_count--;
    spinlock_release(&sem->sem_lock);
}
```

```json
{
  "problem_id": "1b",
  "points": 3,
  "type": "Freeform",
  "tags": ["concurrency", "semaphores"],
  "answer": "The implementation releases the spinlock before acquiring the wait-channel lock, creating a window where no locks are held and the semaphore state can change. The correct ordering is to acquire the wait-channel lock before releasing the spinlock. Example interaction: Thread T1 checks sem_count==0, releases spinlock and is preempted before acquiring wchan lock; Thread T2 performs V and increments sem_count and wakes waiters; when T1 resumes it then sleeps on the wait channel even though sem_count>0.",
  "llm_judge_instructions": "Award 2 points for identifying the incorrect lock ordering and the resulting window where the semaphore state can change; award 1 additional point for providing a correct illustrative sequence of events showing how a thread can end up sleeping despite sem_count>0; 0 points otherwise."
}
```

---

## Question 1c [2 point(s)]

Explain why system calls need to increment the EPC by 4 before returning to user space. Why is incrementing the EPC not necessary when handling other exceptions?

```json
{
  "problem_id": "1c",
  "points": 2,
  "type": "Freeform",
  "tags": ["systems", "exceptions"],
  "answer": "The syscall is a user instruction; returning to the same EPC would re-execute the syscall and immediately cause the same exception again. Incrementing the EPC skips over the syscall instruction so execution resumes at the next user instruction. Other exceptions are typically caused by transient conditions that should be handled and then re-running the instruction may be appropriate, so skipping is not always required.",
  "llm_judge_instructions": "Award 2 points for stating that EPC must be advanced past the syscall to avoid re-triggering it and for explaining why other exceptions may not require advancing EPC; 0 points otherwise."
}
```

---

## Question 1d [2 point(s)]

Explain why a page table entry does not contain a page number, yet a TLB entry contains both a page number and a frame number.

```json
{
  "problem_id": "1d",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "tlb"],
  "answer": "The page number is the implicit index into the page table, so storing it in each PTE would be redundant. The TLB is a cache that stores only a subset of mappings, so each TLB entry must record the page number (or virtual page tag) along with the frame number to identify which virtual page the cached mapping corresponds to.",
  "llm_judge_instructions": "Award 2 points for noting that the PTE uses its table index (redundant to store page number) and that the TLB must store a page identifier because it is a partial cache; 0 points otherwise."
}
```

---

## Question 1e [2 point(s)]

A trapframe contains more information than a switchframe. Why?

```json
{
  "problem_id": "1e",
  "points": 2,
  "type": "Freeform",
  "tags": ["exception-handling", "architecture"],
  "answer": "A switchframe is used for a controlled context switch where function call conventions apply and caller-saved registers need not be preserved. A trapframe must save the entire CPU state since exceptions are asynchronous and there are no calling conventions to rely on; therefore it contains more information.",
  "llm_judge_instructions": "Award 2 points for explaining that trapframes must preserve the full processor state for asynchronous exceptions whereas switchframes rely on calling conventions and save less; 0 points otherwise."
}
```

---

## Question 1f [4 point(s)]

Imagine a version of OS/161 with the following bug: When the exception caused by division by zero is raised, the kernel instead handles it as a system call. What will be the behavior of the following program if the compiler stores n in v0 and d in a0? What will be the behavior if the compiler stores n in a0 and d in v0?

Table of system calls:
System Call | System Call #
pidt fork(void) | 0
pidt vfork(void) | 1
int execv(const char *program, char **args) | 2
void exit(int exitcode) | 3
pidt waitpid(pidt, int *status, int options) | 4
pidt getpid(void) | 5

```c
int main() {
    int n = 6;
    int d;
    for (d = 2; d >= 0; d--)
        n /= d;
    printf("%d\n", d);
    return 0;
}
```

```json
{
  "problem_id": "1f",
  "points": 4,
  "type": "Freeform",
  "tags": ["systems", "exceptions", "os161"],
  "answer": "If the compiler stores n in v0 and d in a0: the division-by-zero trap will be treated as a system call with v0 holding the syscall number; since v0 contains n=6 (not a valid syscall), behavior depends on syscall dispatch but in the intended example the program will exit with exit code 0. If the compiler stores n in a0 and d in v0: the division-by-zero will present v0 equal to d (0) as the syscall number, which may correspond to fork/vfork behavior; in the provided scenario this leads to the program spawning children in a loop with each child printing -1.",
  "llm_judge_instructions": "Award 2 points for correctly describing the first-case behavior and 2 points for correctly describing the second-case behavior. If only one case is correctly described, award partial credit accordingly; 0 points if neither is correct."
}
```

---

## Question 2a [2 point(s)]

What concurrency problem does this program suffer from?

```json
{
  "problem_id": "2a",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "deadlock"],
  "answer": "Deadlock",
  "llm_judge_instructions": "Award 2 points for stating 'Deadlock' and no points otherwise."
}
```

---

## Question 2b [4 point(s)]

Provide a sequence of events that can trigger this problem.

```json
{
  "problem_id": "2b",
  "points": 4,
  "type": "Freeform",
  "tags": ["concurrency", "deadlock"],
  "answer": "Example sequence: Thread 1 calls funcAB and goes to sleep in cv_wait while holding lock A; Thread 3 calls funcAB and acquires lock B first then blocks waiting for lock A; Thread 2 calls funcB and holds lock B; Thread 1 wakes and attempts to take lock B but cannot because Thread 2 holds it, creating a circular wait (A held by Thread 1 waiting for B, B held by Thread 3 or Thread 2 waiting for A), resulting in deadlock.",
  "llm_judge_instructions": "Award 2 points for describing the initial steps that lead to circular wait (e.g., one thread holding A and waiting, another holding B and waiting), and 2 points for explaining how those steps form a circular wait resulting in deadlock. Partial credit only if parts of the sequence or the circular-wait explanation are correct."
}
```

---

## Question 2c [2 point(s)]

What changes to any of the above functions would address this problem?

```json
{
  "problem_id": "2c",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "deadlock-prevention"],
  "answer": "Ensure a consistent lock acquisition order; for example, acquire lock A before lock B in funcAB (or otherwise eliminate the circular wait).",
  "llm_judge_instructions": "Award 2 points for proposing acquiring lock A before lock B in funcAB or an equivalent solution that eliminates circular wait; 0 points otherwise."
}
```

---

## Question 3a [2 point(s)]

In a single-level paged system, how many bits of a virtual memory address would refer to the page number and how many to the offset? How many bits of a physical address would refer to the frame number and how many to the offset?

```json
{
  "problem_id": "3a",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "20-bit page number and 12-bit offset for the virtual address; 36-bit frame number and 12-bit offset for the physical address.",
  "llm_judge_instructions": "Award 2 points for the breakdown: 20-bit virtual page number + 12-bit offset; 36-bit physical frame number + 12-bit offset; 0 points otherwise."
}
```

---

## Question 3b [2 point(s)]

How many bytes would a single-level page table require?

```json
{
  "problem_id": "3b",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "2^23 bytes",
  "llm_judge_instructions": "Award 2 points for the correct byte count 2^23; 0 points otherwise."
}
```

---

## Question 3c [2 point(s)]

If a page table entry contains a frame number, a valid bit, a writable bit, and a single bit for tracking page usage, how many bits per page table entry are unused?

```json
{
  "problem_id": "3c",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "25 bits are unused",
  "llm_judge_instructions": "Award 2 points for 25 bits unused; 0 points otherwise."
}
```

---

## Question 3d [2 point(s)]

How many page table entries fit onto a single page?

```json
{
  "problem_id": "3d",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "512 entries",
  "llm_judge_instructions": "Award 2 points for 512 entries; 0 points otherwise."
}
```

---

## Question 3e [2 point(s)]

What is the minimum number of levels necessary to implement a multi-level paged system if each page table at each level must fit into a single page?

```json
{
  "problem_id": "3e",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "3 levels",
  "llm_judge_instructions": "Award 2 points for 3 levels; 0 points otherwise."
}
```

---

## Question 4a [3 point(s)]

Change the following sketch of an implementation of fork to instead implement vfork. Assume that the appropriate changes are made to execv elsewhere. You may cross out steps and add new steps.

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
  "problem_id": "4a",
  "points": 3,
  "type": "Freeform",
  "tags": ["process-management", "vfork"],
  "answer": "Replace 'copy address space' with linking to the same address space, and ensure the parent is blocked until the child calls execv (or exits).",
  "llm_judge_instructions": "Award 2 points for replacing copying the address space with linking to the same address space, and 1 point for adding that the parent must block until the child reaches execv; 0 points otherwise."
}
```

---

## Question 4b [3 point(s)]

Each change in the semantics of vfork impacts the implementation of execv. How would an implementation of execv need to differ to support both of these changes in vfork?

If process was created with vfork, do not destroy the address space. Signal the parent.

```json
{
  "problem_id": "4b",
  "points": 3,
  "type": "Freeform",
  "tags": ["process-management", "vfork", "execv"],
  "answer": "When execv is called by a process created with vfork, do not immediately destroy or replace the shared address space; instead safely set up the new address space and then notify or signal the parent that it may continue. Ensure any parent blocking is released only after the child's execv setup is complete.",
  "llm_judge_instructions": "Award 2 points for specifying that execv should not immediately destroy the shared address space in the vfork case, and 1 point for stating that the parent must be signaled/unblocked after execv completion; 0 points otherwise."
}
```

---

## Question 4c [2 point(s)]

The documentation for vfork states that the child process shouldn’t return from the function that called vfork. Why not?

```json
{
  "problem_id": "4c",
  "points": 2,
  "type": "Freeform",
  "tags": ["process-management", "vfork", "usability"],
  "answer": "Because the user-space stack and address space are shared between parent and child in vfork; if the child returns from the calling function it will pop the shared stack frame and corrupt the parent's stack/frames, leading to unpredictable behavior.",
  "llm_judge_instructions": "Award 2 points for explaining that the shared user-space stack makes returning from the calling function unsafe/unpredictable; 0 points otherwise."
}
```

---

## Question 5 [16 point(s)]

You have been hired by the city of Waterloo to help solve a modified version of the “traffic intersection” problem for an intersection with significant pedestrian traffic. For safety, instead of allowing vehicles to share the intersection with pedestrians, you are to build a scramble intersection that, under specific conditions, stops vehicular traffic from all directions to allow pedestrians to cross the intersection.

In this problem, pedestrians and vehicles must never be inside the intersection at the same time. Vehicles must also not collide with other vehicles. When a pedestrian arrives at the intersection, he/she must wait until the intersection is clear of vehicles before entering. However, no additional vehicles must be allowed to enter the intersection while a pedestrian is either waiting or inside the intersection.

The intersection consists of two one-way roads: one north-to-south and the other east-to-west. Each vehicle arrives at the intersection from one of two directions (north or east), called its origin. It is trying to pass through the intersection and exit in the opposite direction of its origin, called its destination. Turns for vehicles are not allowed. Because pedestrians cannot collide with other pedestrians and can only cross when there are no vehicles inside the intersection, we do not need to know a pedestrian’s origin or destination.

Implement the following six functions. Global variables can be defined in the provided space. Your solution should be efficient. It should also prioritize pedestrians while providing fairness between vehicles.

(The detailed sample solution has been removed from the exam text; students are expected to implement the synchronization functions based on the specification above.)

```json
{
  "problem_id": "5",
  "points": 16,
  "type": "Freeform",
  "tags": ["operating-systems", "synchronization", "concurrency"],
  "answer": "A correct solution uses synchronization primitives to ensure mutual exclusion between pedestrians and vehicles and to prevent vehicle-vehicle collisions, while prioritizing pedestrians when they are waiting or inside the intersection. One valid approach uses a single lock, per-direction condition variables (dir_cv[2]), a pedestrian condition variable (ped_cv), and state variables: cars_inside[2], cars_waiting[2], ped_inside, ped_waiting, and next_after_ped. Vehicle entry should block if any pedestrians are inside or waiting, or if opposing-direction cars are inside; vehicle exit should wake pedestrians when no cars remain or wake the appropriate vehicle direction otherwise. Pedestrian entry should wait until no cars are inside, increment ped counters, and pedestrian exit should wake waiting cars based on next_after_ped and update next_after_ped to ensure fairness. Proper initialization and cleanup of global synchronization objects is also required.",
  "llm_judge_instructions": "Award up to 16 points as follows: 6 points for a correct intersection_before_vehicle_entry implementation (blocking for ped_inside/ped_waiting and handling per-direction ordering), 4 points for intersection_after_vehicle_exit (correct wakeup logic to favor pedestrians when present and fair vehicle wakeup otherwise), 3 points for intersection_before_pedestrian_entry (waiting until no cars inside, updating ped counters), and 3 points for intersection_after_pedestrian_exit (waking vehicles appropriately and updating next_after_ped for fairness). Points within each part should be awarded only if the synchronization avoids races and deadlock and enforces pedestrian priority; partial credit is allowed when parts are correct independently."
}
```