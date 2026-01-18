# CS530 Spring 2014 Midterm

```json
{
  "exam_id": "cs530_spring_2014_midterm",
  "test_paper_name": "CS530 Spring 2014 Midterm",
  "course": "CS530",
  "institution": "University of Waterloo",
  "year": 2014,
  "score_total": 60,
  "num_questions": 19
}
```

---

## Question 1a [2 point(s)]

a. (2 marks) How many processes, in total, will be created when this program is run, including the original parent process?

Context: Consider the application code below, which uses the fork and waitpid system calls.

Code:
int i;
dofork(){
pid_t pid; int status;
i++;
pid = fork();
if (pid == 0){/* child */
printf("%d",i);
return;
}else{/* parent */
i--;
waitpid(pid,&status,0);
printf("%d",i);
return;
}
}
int main(){
i = 0;
dofork();
dofork();
}

```json
{
  "problem_id": "1a",
  "points": 2,
  "type": "Freeform",
  "tags": ["process-management", "fork"],
  "answer": "Four processes.",
  "llm_judge_instructions": "Award 2 points if the student indicates a total of 4 processes (acceptable answers include '4' or 'Four processes'). Award 0 points otherwise."
}
```

---

## Question 1b [2 point(s)]

b. (2 marks) Show the output that will be produced when this program runs. Note that the statement printf(\"%d\",i); will print the value of integer variable i. You should show the combined output of all processes. Your answer should be a single sequence of numbers.

Context: This is the same program as in 1a.

```json
{
  "problem_id": "1b",
  "points": 2,
  "type": "Freeform",
  "tags": ["process-management", "fork", "output"],
  "answer": "1 2 1 0 1 0",
  "llm_judge_instructions": "Award 2 points for exactly the sequence '1 2 1 0 1 0' (spaces included as shown). Award 0 points otherwise."
}
```

---

## Question 1c [2 point(s)]

c. (2 marks) Suppose that the call to waitpid is removed from the dofork function, and the modified program is then run. Give an example of output that could be produced by this modified program, but that could not be produced by the original, unmodified program. Again, your answer should be a single sequence of numbers. The sequence must include exactly two 0’s, three 1’s, one 2, and nothing else. In addition
• at least one 1 must precede the 2, and
• at least one 0 must precede the last 1

Provide one valid sequence satisfying the constraints.

```json
{
  "problem_id": "1c",
  "points": 2,
  "type": "Freeform",
  "tags": ["process-management", "fork", "output"],
  "answer": "1 1 0 0 2 1",
  "llm_judge_instructions": "Award 2 points if the submitted sequence contains exactly two 0's, three 1's, and one 2, with at least one 1 appearing before the 2 and at least one 0 preceding the final 1. Award 0 points otherwise."
}
```

---

## Question 2a [5 point(s)]

a. (5 marks) In the space below, implement the lock_tryacquire function, which has the following prototype:
int locktryacquire(struct lock *lock);
If the lock is free, locktryacquire should acquire the lock on behalf of the calling thread, and should return 1 to indicate success. If the lock is not free, locktryacquire should do nothing, and should return 0 to indicate failure. Thus, this function is similar to lock_acquire except that it must never cause the calling thread to block. Like lock_acquire and lock_release, locktryacquire must be an atomic operation.

Context: The lock structure is defined as:
struct lock{
    char *lk;
    name;
    struct wchan *wchan;
    struct spinlock spinlock;
    volatile struct thread *holder;
};

```json
{
  "problem_id": "2a",
  "points": 5,
  "type": "Freeform",
  "tags": ["synchronization", "locks", "lock-implementation"],
  "answer": "int locktryacquire(struct lock *lock){\n    spinlock_acquire(&lock->spinlock);\n    if (lock->holder == NULL){\n        lock->holder = curthread;\n        spinlock_release(&lock->spinlock);\n        return 1;\n    }else{\n        spinlock_release(&lock->spinlock);\n        return 0;\n    }\n}",
  "llm_judge_instructions": "Award 5 points for a correct, non-blocking implementation that uses the provided spinlock to atomically check and set lock->holder and returns 1 on success and 0 on failure. If the implementation is functionally equivalent but differs only in formatting, award full credit. Award 0 points for implementations that block, do not use the spinlock to protect lock->holder, or return incorrect values."
}
```

---

## Question 2b [5 point(s)]

b. (5 marks) Suppose that a set of threads is using multiple locks for synchronization. In most cases, threads will acquire and release one lock at a time, using lock_acquire and lock_release. However, in some situations it is necessary for a thread to acquire two locks simultaneously. Write a function called acquiretwolocks that a thread can call to lock two different locks. The function prototype should be as follows:
void acquiretwolocks(struct lock *L1, struct lock *L2)
Before calling this function, the calling thread must not hold either lock. When this call returns, the calling thread should hold both of the specified locks.
Your implementation of acquiretwolocks must satisfy the following requirements:
1. The only synchronization primitives that your implementation may use are the two locks that are passed as input parameters. It may call lock_acquire, lock_release, and/or lock_tryacquire on those locks. (You may use lock_tryacquire here even if you did not implement it for part (a).) It may not use any other synchronization primitives, and it may not use wait channels or test-and-set instructions directly.
2. Your implementation must never “hold and wait”. That is, it must never block or spin while it is holding one of the locks.

```json
{
  "problem_id": "2b",
  "points": 5,
  "type": "Freeform",
  "tags": ["concurrency", "deadlock-avoidance", "locks"],
  "answer": "void acquiretwolocks(struct lock *L1, struct lock *L2){\n    lock_acquire(L1);\n    while ( lock_tryacquire(L2) == 0 ){\n        lock_release(L1);\n        lock_acquire(L1);\n    }\n    return;\n}",
  "llm_judge_instructions": "Award 5 points for an implementation that never holds one lock while blocking for the other and that uses only the two locks passed in (e.g., acquire L1, try to acquire L2 with lock_tryacquire, release L1 and retry until both are held). If the solution uses other synchronization primitives, may deadlock, or fails to guarantee both locks are held on return, award 0 points."
}
```

---

## Question 3a [2 point(s)]

a. (2 marks) In the space below, declare any lock(s), condition variable(s), and shared global variable(s) you will need in your solution to re-implement the CatMouseWait mechanism without semaphores. Be sure to indicate an initial value for any shared global variable(s).

```json
{
  "problem_id": "3a",
  "points": 2,
  "type": "Freeform",
  "tags": ["concurrency", "locks", "condition-variables"],
  "answer": "struct lock *mutex;\nstruct cv *cv;\nvolatile int numanimals = NumCats + NumMice;",
  "llm_judge_instructions": "Award 2 points if the student declares a mutex, a condition variable, and a shared counter initialized to NumCats + NumMice (or equivalent). Award 0 points otherwise."
}
```

---

## Question 3b [3 point(s)]

b. (3 marks) In the space below, show the code that should be used by the master thread to wait for all cats and mice to finish. This should use the variables/locks/condition variable declared in part (a).

```json
{
  "problem_id": "3b",
  "points": 3,
  "type": "Freeform",
  "tags": ["concurrency", "locks", "condition-variables"],
  "answer": "lock_acquire(mutex);\nwhile (numanimals > 0){\n    cv_wait(cv,mutex);\n}\nlock_release(mutex);",
  "llm_judge_instructions": "Award 3 points for correct usage of mutex and condition variable: acquiring the mutex, waiting in a loop until numanimals == 0 using cv_wait, and releasing the mutex. Award partial credit (1-2 points) for solutions that are close but miss one detail (e.g., missing loop). Award 0 points for incorrect approaches."
}
```

---

## Question 3c [3 point(s)]

c. (3 marks) In the space below, show the code that should be used by each cat and mouse thread to indicate that it has finished. This should use the variable(s), lock(s) or condition variable(s) you declared in part (a). Cats and mice must use the same code.

```json
{
  "problem_id": "3c",
  "points": 3,
  "type": "Freeform",
  "tags": ["concurrency", "locks", "condition-variables"],
  "answer": "lock_acquire(mutex);\nnumanimals--;\nif (numanimals == 0){\n    cv_signal(cv,mutex);\n}\nlock_release(mutex);",
  "llm_judge_instructions": "Award 3 points for code that acquires the mutex, decrements numanimals, signals the condition variable when numanimals reaches 0, and releases the mutex. Award partial credit (1-2 points) for solutions that correctly modify numanimals but omit the cv_signal or mutex usage. Award 0 points for incorrect synchronization."
}
```

---

## Question 4 [6 point(s)]

4. (6 total marks) The following assembly language pseudo-code shows how the load-linked (ll) and store-conditional (sc) instructions can be used together to test-and-set a lock. In this code, &lock represents the address of the lock variable. The comments remind you how the ll and sc instructions behave.
// load the value 1 into register R1
li R1,1
// load the value of the lock variable into register R0
ll R0,&lock
// if the value of the lock variable has not changed since the ll
// instruction, store the value in R1 into the lock variable and
// set the value in R1 to 1 to indicate success. Otherwise,
// do not change the value of the lock variable and set the value
// of R1 to 0 to indicate failure.
sc R1,&lock

Suppose that a thread T executes these instructions as part of a call to spinlock_acquire. Immediately after T executes the sc instructions, there are four possible situations, depending on the values in the registers R0 and R1. The table below lists these four possible situations. For each situation, indicate which of the following statements is true:
• Holds the lock.
• Some thread other than T holds the lock.
• No thread holds the lock.
• Not possible to determine whether the lock is held.
Indicate your answers by writing the correct statement in each box. The same statement may appear in more than one box.

Value of R0 | Value of R1 | Statement
------------------------------------
0 | 0 | _____
0 | 1 | _____
1 | 0 | _____
1 | 1 | _____

```json
{
  "problem_id": "4",
  "points": 6,
  "type": "Freeform",
  "tags": ["assembly", "ll_sc", "test_and_set"],
  "answer": "R0=0, R1=0: Not possible to determine whether the lock is held.\nR0=0, R1=1: Holds the lock.\nR0=1, R1=0: Not possible to determine whether the lock is held.\nR0=1, R1=1: Some thread other than T holds the lock.",
  "llm_judge_instructions": "Award 6 points total: 2 points for each correctly filled table entry. Specifically, award 2 points for correctly identifying the statement for (R0=0,R1=1), 2 points for (R0=1,R1=1), and 2 points for the remaining two cases as 'Not possible to determine whether the lock is held.' Partial credit may be given per correctly answered row."
}
```

---

## Question 5 [6 point(s)]

5. (6 total marks) Suppose that two different types of processes, crunchers and talkers, run in a system. The system has a single processor, and it uses preemptive round-robin scheduling, with a scheduling quantum of q time units. Crunchers never block. When they are chosen to run by the scheduler, they will run until they are preempted. Talkers, on the other hand, continuously output characters, as illustrated by the following pseudo-code:
while (true){
/* output a character */
}
Each time a talker outputs a character, it blocks for b time units while the character is being output, before becoming ready again. Assume that the actual execution time (time spent in the “running” state) for each iteration of the talker is very small - much smaller than b.
Answer each of the following questions about this system. Express your answers in terms of b and q. Assume that b < q.

a. (2 marks) Suppose that there is one talker process in the system, and no other processes. How long will it take the talker to output 100 characters?

b. (2 marks) Suppose that there is one talker and one cruncher running in the system. How much time will elapse before the talker outputs 100 characters?

c. (2 marks) Suppose that one talker and k (k > 0) crunchers are running in the system. How much time will elapse before the talker outputs 100 characters? Express your answer in terms of k, b and q.

```json
{
  "problem_id": "5",
  "points": 6,
  "type": "Freeform",
  "tags": ["scheduling", "rr", "concurrency"],
  "answer": "a) 100*b\nb) 100*q\nc) 100*k*q",
  "llm_judge_instructions": "Award 2 points for each correct expression: (a) 100*b, (b) 100*q, (c) 100*k*q. Partial credit (1 point) may be awarded for answers that are close or show correct reasoning but minor mistakes."
}
```

---

## Question 6 [8 point(s)]

6. (8 total marks) Suppose threads in a concurrent program share access to two different FIFO queues of data, QueueA and QueueB. There are two functions that threads use to move data items between the two queues:
• AtoB():  this function dequeues one item from QueueA and enqueues that item onto QueueB
• BtoA():  this function dequeues one item from QueueB and enqueues that item onto QueueA
Suppose that, initially, QueueA contains N data items, and QueueB is empty.
Your job is to insert semaphore operations (P and V) into the provided skeleton implementations of AtoB() and BtoA() so that the following requirements are satisfied:
1. dequeue() should never be run on an empty queue.
2. At most one thread at a time should be using each queue. For example, if one thread is running dequeue() on QueueA, no other thread should be running dequeue() or enqueue() on QueueA.
3. Items must be enqueued onto QueueB in the same order that they are dequeued from QueueA. Similarly, items must be enqueued onto QueueA in the same order that they are dequeued from QueueB.
4. Threads must never deadlock.
In addition, allow concurrent usage of different queues when possible (i.e., do not use a single semaphore to lock both queues).
Add semaphore operations (P and V) to the skeleton code so that these synchronization requirements will be satisfied. Do not use any synchronization primitives other than semaphores in your solution. Do not make any changes to the skeleton code other than inserting calls to semaphore operations.

(Insert P and V calls in the skeleton code provided in the exam.)

```json
{
  "problem_id": "6",
  "points": 8,
  "type": "Freeform",
  "tags": ["semaphores", "producer-consumer", "synchronization"],
  "answer": "Students should declare semaphores to count items and provide mutual exclusion for each queue, and then insert P and V operations into AtoB() and BtoA() to ensure: (1) dequeue is preceded by the appropriate count semaphore P, (2) each queue is protected by a mutex semaphore during dequeue/enqueue, (3) transfers preserve order by protecting the dequeue/enqueue sequence, and (4) the scheme avoids deadlock (e.g., by ordering or by ensuring a thread does not hold one mutex while waiting on a count semaphore for the other queue).",
  "llm_judge_instructions": "Award up to 8 points using the following rubric: (1) 2 points for correctly preventing dequeue on an empty queue using counting semaphores (Acount/Bcount). (2) 2 points for ensuring mutual exclusion per queue (Amutex/Bmutex usage). (3) 2 points for preserving the order of transfer between queues (correct placement of mutexes around dequeue+enqueue to maintain FIFO ordering). (4) 2 points for avoiding deadlock while allowing concurrent use of different queues when possible (e.g., correct use of additional per-direction mutexes or retrying without holding other queue mutexes). Partial credit within each item may be awarded if the student's solution partially satisfies the item."
}
```

---

## Question 7a [3 point(s)]

a. (3 total marks) Which of the following effects does a MIPS syscall instruction have when it is executed? (Note: we are interested only in the effects of this single instruction, not the effects of any code that runs after this instruction.) Circle all that apply.
- the current value of the program counter is saved
- a trap frame is saved
- the processor switches to privileged execution mode
- the current thread stops running
- a timer interrupt occurs
- an error code is returned to the application
- the value of the program counter is changed

```json
{
  "problem_id": "7a",
  "points": 3,
  "type": "Freeform",
  "tags": ["syscalls", "mips", "kernel"],
  "answer": "the current value of the program counter is saved; a trap frame is saved; the processor switches to privileged execution mode; the current thread stops running; the value of the program counter is changed",
  "llm_judge_instructions": "Award 3 points if the student lists these five effects: the current value of the program counter is saved; a trap frame is saved; the processor switches to privileged execution mode; the current thread stops running; and the value of the program counter is changed. Award 0 points otherwise."
}
```

---

## Question 7b [2 point(s)]

b. (2 total marks) Neither threads that are in the ready state nor threads that are in the blocked state are running. What is the difference between these two states?

```json
{
  "problem_id": "7b",
  "points": 2,
  "type": "Freeform",
  "tags": ["scheduling", "threads"],
  "answer": "A ready thread is runnable, and will run again as soon as the scheduler chooses it to run. A blocked thread will not become runnable again until another process wakes it up (via a call to wchan_wakeone or wchan_wakeall).",
  "llm_judge_instructions": "Award 2 points for the distinction that a ready thread is runnable and awaits scheduling, whereas a blocked thread will not become runnable until explicitly woken. Award 0 points otherwise."
}
```

---

## Question 7c [2 point(s)]

c. (2 total marks) Explain why disabling interrupts may not enforce mutual exclusion on a multi-processor machine.

```json
{
  "problem_id": "7c",
  "points": 2,
  "type": "Freeform",
  "tags": ["cpu-modes", "mutual-exclusion"],
  "answer": "Disabling interrupts on one processor will not prevent a thread running on another processor from entering the critical section.",
  "llm_judge_instructions": "Award 2 points for explaining that disabling interrupts on one CPU does not affect other CPUs, so it does not prevent concurrent entry to a critical section on multi-processor systems. Award 0 points otherwise."
}
```

---

## Question 7d [1 point(s)]

d. (1 total marks) If a thread avoids “holding and waiting”, then that thread will never be involved in a deadlock. True or false?

```json
{
  "problem_id": "7d",
  "points": 1,
  "type": "Freeform",
  "tags": ["deadlock"],
  "answer": "False.",
  "llm_judge_instructions": "Award 1 point for the answer 'False'. Award 0 points otherwise."
}
```

---

## Question 7e [1 point(s)]

e. (1 total marks) If all threads avoid “holding and waiting”, then no thread will ever be involved in a deadlock. True or false?

```json
{
  "problem_id": "7e",
  "points": 1,
  "type": "Freeform",
  "tags": ["deadlock"],
  "answer": "True.",
  "llm_judge_instructions": "Award 1 point for the answer 'True'. Award 0 points otherwise."
}
```

---

## Question 7f [3 point(s)]

f. (3 total marks) We have identified three types of events that cause execution control to transfer from an application program to the kernel. What are those three types of events?

```json
{
  "problem_id": "7f",
  "points": 3,
  "type": "Freeform",
  "tags": ["kernel", "events"],
  "answer": "System calls, interrupts, and exceptions.",
  "llm_judge_instructions": "Award 3 points for listing 'system calls', 'interrupts', and 'exceptions'. Award 0 points otherwise."
}
```

---

## Question 7g [2 point(s)]

g. (2 total marks) Suppose that a process P calls waitpid and blocks because the process it is waiting for is still running. At the time that P blocks, how many trap frames will be on P’s thread’s stacks, and which stack, or stacks, will those trap frames be found on? Briefly justify your answer.

```json
{
  "problem_id": "7g",
  "points": 2,
  "type": "Freeform",
  "tags": ["traps", "kernel-stack"],
  "answer": "One trap frame, on P’s thread’s kernel stack; it was created when P’s thread switched to kernel mode to handle waitpid.",
  "llm_judge_instructions": "Award 2 points for stating that there is one trap frame on P's thread's kernel stack and providing the justification that it was created when the thread entered kernel mode to perform the system call. Award 0 points otherwise."
}
```

---

## Question 7h [2 point(s)]

h. (2 total marks) For the same situation described in part (g), how many switch frames will be on P’s thread’s stacks, and which stack, or stacks, will those switch frames be found on? Briefly justify your answer.

```json
{
  "problem_id": "7h",
  "points": 2,
  "type": "Freeform",
  "tags": ["thread-switching", "kernel-stack"],
  "answer": "One switch frame, on P’s thread’s kernel stack.",
  "llm_judge_instructions": "Award 2 points for stating that there is one switch frame on P's thread's kernel stack and briefly justifying that it was created when the thread blocked and the scheduler switched to another thread. Award 0 points otherwise."
}
```