# CS 530 Winter 2015 Midterm

```json
{
  "exam_id": "cs530_winter_2015_midterm",
  "test_paper_name": "CS 530 Winter 2015 Midterm",
  "course": "CS 530",
  "institution": "University of Waterloo",
  "year": 2015,
  "score_total": 75,
  "num_questions": 11
}
```

---

## Question 1 [9 point(s)]

For the program shown below, assume that all function, library and system calls are successful. Recall that
the prototype/signature for thread_fork is:
int thread_fork(const char *name, struct proc *proc,
void (*func)(void *, unsigned long),
void *data1, unsigned long data2);
volatile int x = 42;
main()
{
/* name="1", no process, runs func1 */
/* parameters 0 and 0, not used */
thread_fork("1",NULL,func1,0,0);
/* name="2", no process, runs func2 */
/* parameters 0 and 0, not used */
thread_fork("2",NULL,func2,0,0);
func3(0,0);
}
void func1(unsigned long notused, void *notused2)
{
kprintf("A: %d\n", x);
x = 10;
}
void func2(unsigned long notused, void *notused2)
{
kprintf("B: %d\n", x);
x = 20;
}
void func3(unsigned long notused, void *notused2)
{
kprintf("C: %d\n", x);
x = 30;
}
When considering each line of output produced by the program above, what would the output be when
printing the value of the variable x? If more than one value or a range of values is possible, list all possible
values or ranges.
From func1: A:
From func2: B:
From func3: C:

```json
{
  "problem_id": "1",
  "points": 9,
  "type": "Freeform",
  "tags": ["os", "threading", "concurrency"],
  "answer": "A: 42 | 20 | 30\nB: 42 | 10 | 30\nC: 42 | 10 | 20",
  "llm_judge_instructions": "Total 9 points. Award 3 points for each correct line (A, B, C). For each line, the grader should compare the student's exact listed set of possible values for that line to the expected set. If the student's line exactly matches the expected string for that line, award 3 points; otherwise award 0 for that line. (3 pts × 3 lines = 9 pts)"
}
```

---

## Question 2 [14 point(s)]

For the program shown below, what output would be printed when it runs? If a range or multiple values are
possible, give the range or possible values. If it is not possible to determine the value, possible values or a
range, state so and explain why. Assume that all function, library and system calls are successful. If more than
one ordering of output is possible choose one of the possible orderings. Recall that WEXITSTATUS(status) just
gets the exit code portion of the status variable.
int x = 42;
main()
{
int rc, status;
rc = fork();
if (rc == 0) {
func1();
_exit(1);
} else {
rc = waitpid(rc, &status, 0);
printf("R: %d", WEXITSTATUS(status));
printf("M: %d\n", x);
x = 100;
printf("P: %d\n", x);
_exit(2);
}
func2();
}
void func1()
{
int rc, status;
printf("T: %d\n", x);
x = 10;
rc = fork();
if (rc == 0) {
x = 50;
printf("Q: %d\n", x);
_exit(3);
}
rc = waitpid(rc, &status, 0);
printf("A: %d\n", x);
printf("D: %d", WEXITSTATUS(status));
_exit(4);
}
void func2()
{
printf("C: %d\n", x);
}

```json
{
  "problem_id": "2",
  "points": 14,
  "type": "Freeform",
  "tags": ["c", "processes", "fork", "wait"],
  "answer": "T: 42\nQ: 50\nA: 10\nD: 3\nR: 4\nM: 42\nP: 100",
  "llm_judge_instructions": "Total 14 points. There are 7 expected output lines (T, Q, A, D, R, M, P). Award 2 points for each line that exactly matches the expected output (including formatting and values). No points for a mismatched line. Full credit requires all 7 lines correct (7 × 2 = 14)."
}
```

---

## Question 3 [12 point(s)]

Problem 3 (12 marks)
The diagram below shows a number of threads executing on two different CPUs (the names of each thread are
shown). The vertical lines indicate context switches between two threads and the labels at those vertical lines
indicate the time at which the context switch occurred.
T1 T3 T1 T5 T3
CPU 1
CPU 0
D
E
F
G
H
C A
B
T1 T2 T3 T5 T2
In OS/161 a context switch is initiated by a call to thread_switch. That function determines which thread
to run next (pointed to by next) and calls switchframe_switch which performs the context switch from the
current thread (pointed to by cur) to the next thread (pointed to by next). In the code below we have added
two kprintf calls to print out the names of the cur and next thread before and after the context switch.
kprintf("Before: cur = %s next = %s\n", cur->t_name, next->t_name);
/* do the switch (in assembler in switch.S) */
switchframe_switch(&cur->t_context, &next->t_context);
kprintf("After: cur = %s next = %s\n", cur->t_name, next->t_name);
Using the diagram at the top of the page and the code above fill in the output that would be produced after
each call to switchframe_switch (the output for the “Before” print statement has been provided). If it is
not possible to determine the answer from the information provided in the diagram use the label “UN” (for
unknown).

Before   After
Time
cur next cur next
A T1 T2
E T3 T2
G T2 T5
H T1 T3

```json
{
  "problem_id": "3",
  "points": 12,
  "type": "Freeform",
  "tags": ["os161", "thread-switching"],
  "answer": "Before: cur = A T next = T1\nAfter: cur = A T next = T2\nBefore: cur = E T next = T3\nAfter: cur = E T next = T2\nBefore: cur = G T next = T2\nAfter: cur = G T next = T5\nBefore: cur = H T next = T1\nAfter: cur = H T next = T3",
  "llm_judge_instructions": "Total 12 points. There are 4 Before/After pairs. Award 3 points for each pair where both the Before and After outputs exactly match the expected strings for that switch. If either part of the pair is incorrect, award 0 for that pair. (4 pairs × 3 pts = 12 pts.)"
}
```

---

## Question 4 [10 point(s)]

Problem 4 (10 marks)
Assume a user-level process (named P1) executes the code shown below on OS/161.
main()         Q()                    R()                     S()
{              {                      {                       {  int i, x;
Q();            int x = getpid();      int y = getpid();       for (i=0;i<N;i++) {
R(); x = x + i;
S();}
}              }                      }                       }
In the rectangles shown for each part of this question below, fill in and label any information about the state of
the kernel stack for the executing process (P1) as it would appear at the point in time stated in the question.
Do not draw anything that has been popped from the stack (is no longer active) and use the same level of
detail used in class and the course notes. If they are present, be sure to show trap frames, switch frames, and
stack frames. Draw the stack so that the high addresses are at the top of the diagram and low addresses are at the bottom. Recall that the stack grows from high addresses to low.

a.(5 mark(s)) The process P1 calls int y = getpid() in the function R. While in the kernel syscall function an interrupt occurs. Show what the contents of the stack look like just prior to returning from the interrupt handler and before popping the stack.

Kernel Stack (show the active frames only)

b.(5 mark(s)) The process P1 is executing function S, an interrupt occurs, the kernel determines that the
thread has reached its quantum of CPU time and it context switches to a thread of process P2. Show
what the kernel stack looks like for P1 after the context switch to P2.

Kernel Stack (show the active frames only)

```json
{
  "problem_id": "4",
  "points": 10,
  "type": "Freeform",
  "tags": ["os161", "kernel-stack"],
  "answer": "a) Expected stack contents (top to bottom): trap frame from system call (from user->kernel entry); syscall stack frame(s) (e.g., getpid/syscall handler); trap frame created by the interrupt; interrupt handler stack frame(s). b) Expected stack contents (for P1 after being preempted): trap frame from interrupt at top, any interrupted kernel frames beneath (e.g., S's kernel stack frames), a saved switchframe for context switch (switchframe_switch saved state), and remaining kernel stack frames below. The exact number/names of frames may vary, but these elements should be present and ordered with the interrupt-related frames at the top.",
  "llm_judge_instructions": "Total 10 points. Award 5 points for part (a) and 5 points for part (b). Part (a) rubric (5 pts): 2 pts for including the trap frame from the system call, 1 pt for showing the syscall handler/kernel stack frames, 1 pt for including the interrupt's trap frame, and 1 pt for including the interrupt handler frame(s). Part (b) rubric (5 pts): 2 pts for including the interrupt trap frame at top, 1 pt for showing the remaining kernel frames for the interrupted thread (S), and 2 pts for showing the saved switch/context frames (switchframe) left on the stack after the context switch. Partial credit: award points per rubric item as listed. Exact textual matching is not required; grade according to presence and correct ordering of the listed elements."
}
```

---

## Question 5 [12 point(s)]

Problem 5 (12 marks)
Barrier synchronization can be used to prevent threads from proceeding until a specified number of threads
have reached the barrier. Threads reaching the barrier block until the last of the specified number of threads
has reached the barrier, at which point all threads can proceed. Below is a partial pseudocode example of how
barrier synchronization might be used.
/* Used to wait for all mice to be ready to all attack together */
struct barrier *attack_barrier;
/* Used to wait for all mice and the main thread so they can all go to the bar together */
struct barrier *bar_barrier;
main()
{
unsigned int i;
attack_barrier = barrier_create(NUM_MICE);
bar_barrier = barrier_create(NUM_MICE+1);
for (i=0; i<NUM_MICE; i++) {
thread_fork("MightyMouse", mouse, NULL, i);
}
/* Wait here until all threads are ready to go to the bar */
barrier_wait(bar_barrier);
go_to_bar();
}
void
mouse(void *unused, unsigned long mouse_num)
{
unsigned int i;
/* Attack the cats a number of times */
for (i=0; i<ATTACK_COUNT; i++) {
get_ammo(mouse_num);
barrier_wait(attack_barrier); /* wait until all mice are ready to attack */
attack_cats();
}
/* Wait here until all threads are ready to go to the bar */
barrier_wait(bar_barrier);
go_to_bar();
}
Fill in the spaces below (or on the next page) to complete the implementation of a barrier. (You will not
implement barrier_destroy). You must only use locks and condition variables for synchronization (as
they are defined in OS/161). To simplify the code, assume that all calls to kmalloc and to create any required
objects always succeed.

struct barrier {
};
/* Create a barrier that can be used with thread_count threads */
struct barrier *barrier_create(unsigned int thread_count)
{
}
/* Callers wait here until the number of threads specified have */
/* reached this point, then they all proceed. */
void
barrier_wait(struct barrier *b)
{
}

```json
{
  "problem_id": "5",
  "points": 12,
  "type": "Freeform",
  "tags": ["os/161", "barrier", "synchronization"],
  "answer": "Expected implementation details: struct barrier should contain an unsigned int thread_count (expected number), an unsigned int count (current arrived threads), a struct lock *b_lock, and a struct cv *b_cv. barrier_create should allocate the struct, initialize thread_count, set count=0, create a lock and a CV. barrier_wait should acquire the lock, increment count, if count < thread_count then cv_wait(b_cv, b_lock), else (count == thread_count) perform cv_broadcast(b_cv, b_lock) and reset count to 0 to allow reuse, then release the lock.",
  "llm_judge_instructions": "Total 12 points. Grading rubric: 3 pts for correct struct fields (thread_count, count, lock, cv), 3 pts for correct initialization in barrier_create (allocation, set thread_count, count=0, create lock and cv), 6 pts for barrier_wait implementation: 2 pts for acquiring the lock and incrementing count correctly, 2 pts for using cv_wait for threads that arrive before the last, and 2 pts for when the last thread arrives, doing cv_broadcast (or cv_signal to all) and resetting state for reuse, and releasing the lock. Partial credit awarded per item above."
}
```

---

## Question 6a [3 point(s)]

a.(3 mark(s)) The physical address that results from a load from virtual address = 6 125 273 127 604

```json
{
  "problem_id": "6a",
  "points": 3,
  "type": "Freeform",
  "tags": ["tlb", "virtual-memory"],
  "answer": "TLB miss due to invalid bit for the corresponding VPN; translation not possible; exception occurs.",
  "llm_judge_instructions": "Total 3 points. Award full 3 points if the student correctly states that the translation cannot be performed due to a TLB/page invalid bit and that an exception occurs. Award 0 otherwise."
}
```

---

## Question 6b [3 point(s)]

b.(3 mark(s)) The physical address that results from a store to virtual address = 0 000 061 252 127.

```json
{
  "problem_id": "6b",
  "points": 3,
  "type": "Freeform",
  "tags": ["tlb", "virtual-memory"],
  "answer": "Resulting physical address: 30 130 252 127 (translation of VPN to frame 30 130 with offset 252 127).",
  "llm_judge_instructions": "Total 3 points. Award full 3 points if the student provides the correct translated physical address as stated (or equivalent numeric/hex representation). Award 0 if incorrect."
}
```

---

## Question 6c [3 point(s)]

c.(3 mark(s)) Can a store be performed on the physical address = 61 252 612 522? If yes, provide the
virtual address used to access this physical address and if not explain precisely why not.

```json
{
  "problem_id": "6c",
  "points": 3,
  "type": "Freeform",
  "tags": ["tlb", "virtual-memory"],
  "answer": "Yes. An example corresponding virtual address is 0 000 612 612 522 (VPN maps to frame 61 252 which is present and valid).",
  "llm_judge_instructions": "Total 3 points. Award 3 points if the student correctly states that the store is possible and provides a valid corresponding virtual address mapping to the given physical frame. Award 0 if incorrect or if they incorrectly state it is not possible."
}
```

---

## Question 7a [3 point(s)]

a.(3 mark(s)) Translate the Virtual Address 0x4 0017 6429 to a Physical Address.

```json
{
  "problem_id": "7a",
  "points": 3,
  "type": "Freeform",
  "tags": ["virtual-memory", "address-translation"],
  "answer": "0x100176429",
  "llm_judge_instructions": "Total 3 points. Award full 3 points for the exact translated physical address 0x100176429 (or an exact numeric equivalent). Award 0 otherwise."
}
```

---

## Question 7b [3 point(s)]

b.(3 mark(s)) Translate the Virtual Address 0x0 5200 AB25 to a Physical Address.

```json
{
  "problem_id": "7b",
  "points": 3,
  "type": "Freeform",
  "tags": ["virtual-memory", "address-translation"],
  "answer": "No translation possible: address is not part of any valid segment.",
  "llm_judge_instructions": "Total 3 points. Award 3 points if the student correctly states that there is no valid translation because the address is not in any defined segment. Award 0 otherwise."
}
```

---

## Question 7c [3 point(s)]

c.(3 mark(s)) If possible, determine the user space Virtual Address that could be used to access the
Physical Address 0x8 0128 95FA.

```json
{
  "problem_id": "7c",
  "points": 3,
  "type": "Freeform",
  "tags": ["virtual-memory", "address-translation"],
  "answer": "0x3012895FA",
  "llm_judge_instructions": "Total 3 points. Award full 3 points if the student provides the correct corresponding user-space virtual address 0x3012895FA (or exact equivalent). Award 0 otherwise."
}
```