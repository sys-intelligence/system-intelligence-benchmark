# CS350 Spring 2014 Midterm

```json
{
  "exam_id": "cs350_spring_2014_midterm",
  "test_paper_name": "CS350 Spring 2014 Midterm",
  "course": "CS350",
  "institution": "University of Waterloo",
  "year": 2014,
  "score_total": 60,
  "num_questions": 19
}
```

---

## Question 1a [2 point(s)]

a. (2 marks)How many processes, in total, will be created when this program is run, including the original parent process?

```json
{
  "problem_id": "1a",
  "points": 2,
  "type": "Freeform",
  "tags": ["process","fork"],
  "answer": "Four processes.",
  "llm_judge_instructions": "Award 2 points for the exact answer 'Four processes.' (case-insensitive). Award 0 points otherwise."
}
```

---

## Question 1b [2 point(s)]

b. (2 marks)Show the output that will be produced when this program runs.  Note that the statement printf(\"%d\",i); will print the value of integer variable i.  You should show the combined output of all processes. Your answer should be a single sequence of numbers.

```json
{
  "problem_id": "1b",
  "points": 2,
  "type": "Freeform",
  "tags": ["process","output"],
  "answer": "1 2 1 0 1 0",
  "llm_judge_instructions": "Award 2 points for exactly the sequence '1 2 1 0 1 0' (numbers separated by single spaces). 0 points otherwise."
}
```

---

## Question 1c [2 point(s)]

c. (2 marks)Suppose that the call to waitpid is removed from the dofork function, and the modified program is then run.  Give an example of output that could be produced by this modified program, but that could not be produced by the original, unmodified program.  Again, your answer should be a single sequence of numbers.
The sequence must include exactly two 0’s, three 1’s, one 2, and nothing else.  In addition:
- at least one 1 must precede the 2, and
- at least one 0 must precede the last 1.

```json
{
  "problem_id": "1c",
  "points": 2,
  "type": "Freeform",
  "tags": ["process","output","fork","wait"],
  "answer": "1 1 0 0 2 1",
  "llm_judge_instructions": "Award 2 points for exactly the sequence '1 1 0 0 2 1' (numbers separated by single spaces). 0 points otherwise."
}
```

---

## Question 2a [5 point(s)]

a. (5 marks)In the space below, implement the lock tryacquire function, which has the following prototype:
int locktryacquire(struct lock *lock);
If the lock is free, locktryacquire should acquire the lock on behalf of the calling thread, and should return 1 to indicate success.  If the lock is not free, locktryacquire should do nothing, and should return 0 to indicate failure.  Thus, this function is similar to lockacquire except that it must never cause the calling thread to block.  Like lockacquire and lockrelease, locktryacquire must be an atomic operation.

```json
{
  "problem_id": "2a",
  "points": 5,
  "type": "Freeform",
  "tags": ["locks","synchronization","lock-tryacquire"],
  "answer": "int locktryacquire(struct lock *lock){\n/* skeleton expected: non-blocking acquire */\n// Implementation should acquire the lock's spinlock,\n// if holder is NULL set holder to current thread and return 1,\n// else release and return 0.\n}\n",
  "llm_judge_instructions": "Award 2 points for correctly acquiring and releasing the spinlock (atomic protection) when checking lock->holder. Award 2 points for correctly setting lock->holder to the current thread when it is NULL and ensuring no blocking. Award 1 point for returning 1 on success and 0 on failure and not causing the caller to block. Total 5 points."
}
```

---

## Question 2b [5 point(s)]

b. (5 marks)Suppose that a set of threads is using multiple locks for synchronization. In most cases, threads will acquire and release one lock at a time, using lockacquire and lockrelease. However, in some situations it is necessary for a thread to acquire two locks simultaneously. Write a function called acquiretwolocks that a thread can call to lock two different locks. The function prototype should be as follows:
void acquiretwolocks(struct lock *L1, struct lock *L2)
Before calling this function, the calling thread must not hold either lock. When this call returns, the calling thread should hold both of the specified locks.
Your implementation of acquiretwolocks must satisfy the following requirements:
1. The only synchronization primitives that your implementation may use are the two locks that are passed as input parameters. Your implementation may call lockacquire, lockrelease, and/or locktryacquire on those locks. (You may use locktryacquire here even if you did not implement it for part (a).) It may not use any other synchronization primitives, and it may not use wait channels or test-and-set instructions directly.
2. Your implementation must never “hold and wait”. That is, it must never block or spin while it is holding one of the locks.
Keep your implementation as simple as possible. Overly long or complex solutions may be penalized.

```json
{
  "problem_id": "2b",
  "points": 5,
  "type": "Freeform",
  "tags": ["locks","deadlock","synchronization"],
  "answer": "void acquiretwolocks(struct lock *L1, struct lock *L2){\n    lockacquire(L1);\n    while ( locktryacquire(L2) == 0 ){\n        lockrelease(L1);\n        lockacquire(L1);\n    }\n    return;\n}\n",
  "llm_judge_instructions": "Award 2 points for using only the provided locks and only calling lockacquire/lockrelease/locktryacquire. Award 2 points for ensuring the implementation never holds-and-waits (i.e., releases L1 while trying to acquire L2). Award 1 point for correctness/termination (eventually acquiring both locks when possible). Total 5 points."
}
```

---

## Question 3a [2 point(s)]

a. (2 marks)In the space below, declare any lock(s), condition variable(s), and shared global variable(s) you will need in your solution. Be sure to indicate an initial value for any shared global variable(s).

```json
{
  "problem_id": "3a",
  "points": 2,
  "type": "Freeform",
  "tags": ["locks","concurrency","cv"],
  "answer": "struct lock *mutex;\nstruct cv *cv;\nvolatile int numanimals = NumCats + NumMice;",
  "llm_judge_instructions": "Award 1 point for declaring a mutex (or equivalent lock). Award 1 point for declaring a condition variable and initializing numanimals to NumCats + NumMice. Total 2 points."
}
```

---

## Question 3b [3 point(s)]

b. (3 marks)In the space below, show the code that should be used by the master thread to wait for all cats and mice to finish. This should use the variable(s), lock(s) or condition variable(s) you declared in part (a).

```json
{
  "problem_id": "3b",
  "points": 3,
  "type": "Freeform",
  "tags": ["locks","cv","synchronization"],
  "answer": "lockacquire(mutex);\nwhile (numanimals > 0){\n    cvwait(cv, mutex);\n}\nlockrelease(mutex);",
  "llm_judge_instructions": "Award 2 points for using lockacquire and a while loop that checks numanimals>0 with cvwait inside. Award 1 point for releasing the lock after the wait. Total 3 points."
}
```

---

## Question 3c [3 point(s)]

c. (3 marks)In the space below, show the code that should be used by each cat and mouse thread to indicate that it has finished. This should use the variable(s), lock(s) or condition variable(s) you declared in part (a). Cats and mice must use the same code.

```json
{
  "problem_id": "3c",
  "points": 3,
  "type": "Freeform",
  "tags": ["locks","cv","synchronization"],
  "answer": "lockacquire(mutex);\nnumanimals--;\nif (numanimals == 0){\n    cvsignal(cv,mutex);\n}\nlockrelease(mutex);",
  "llm_judge_instructions": "Award 2 points for acquiring the mutex and correctly decrementing numanimals. Award 1 point for signaling the condition variable when numanimals==0 and releasing the mutex. Total 3 points."
}
```

---

## Question 4 [6 point(s)]

4 (6 total marks)The following assembly language pseudo-code shows how the load linked (ll) and store conditional (sc) instructions can be used together to test-and-set a lock. In this code, &lock represents the address of the lock variable. The comments remind you how the ll and sc instructions behave.
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

Suppose that a thread T executes these instructions as part of a call to spinlock_acquire. Immediately after T executes the sc instruction, there are four possible situations, depending on the values in the registers R0 and R1.

The table below lists these four possible situations. For each situation, indicate which of the following statements is true:
- T holds the lock.
- Some thread other than T holds the lock.
- No thread holds the lock.
- Not possible to determine whether the lock is held.

Fill in the statement for each row.

Value of R0 | Value of R1 | Statement
0 | 0 | __________
0 | 1 | __________
1 | 0 | __________
1 | 1 | __________

```json
{
  "problem_id": "4",
  "points": 6,
  "type": "Freeform",
  "tags": ["ll-sc","cpu-architecture","locking"],
  "answer": "\"00: Not possible to determine whether the lock is held.\"; \"01: Tholds the lock.\"; \"10: Not possible to determine whether the lock is held.\"; \"11: Some thread other than Tholds the lock.\"",
  "llm_judge_instructions": "Award 1 point for the correct statement for R0=0,R1=0; 2 points for the correct statement for R0=0,R1=1; 1 point for the correct statement for R0=1,R1=0; and 2 points for the correct statement for R0=1,R1=1. Total 6 points."
}
```

---

## Question 5 [6 point(s)]

5 (6 total marks)Suppose that two different types of processes, crunchers and talkers, run in a system. The system has a single processor, and it uses preemptive round-robin scheduling, with a scheduling quantum of q time units.
Crunchers never block. When they are chosen to run by the scheduler, they will run until they are preempted. Talkers, on the other hand, continuously output characters, as illustrated by the following pseudo-code:
while (true){
/* output a character */
}
Each time a talker outputs a character, it blocks for b time units while the character is being output, before becoming ready again. Assume that the actual execution time (time spent in the “running” state) for each iteration of the talker is very small - much smaller than b.
Answer each of the following questions about this system. Express your answers in terms of b and q. Assume that b < q.

a. (2 marks)Suppose that there is one talker process in the system, and no other processes. How long will it take the talker to output 100 characters?

b. (2 marks)Suppose that there is one talker and one cruncher running in the system. How much time will elapse before the talker outputs 100 characters?

c. (2 marks)Suppose that one talker and k (k > 0) crunchers are running in the system. How much time will elapse before the talker outputs 100 characters? Express your answer in terms of k, b and q.

```json
{
  "problem_id": "5",
  "points": 6,
  "type": "Freeform",
  "tags": ["cpu-scheduling","round-robin","preemption"],
  "answer": "a) 100b\nb) 100q\nc) 100kq",
  "llm_judge_instructions": "Award 2 points for each correct part. a) 2 points if '100b' is given. b) 2 points if '100q' is given. c) 2 points if '100kq' is given. Total 6 points."
}
```

---

## Question 6 [8 point(s)]

6 (8 total marks)Suppose threads in a concurrent program share access to two different FIFO queues of data, QueueA and QueueB. There are two functions that threads use to move data items between the two queues:
- AtoB(): this function dequeues one item from QueueA and enqueues that item onto QueueB
- BtoA(): this function dequeues one item from QueueB and enqueues that item onto QueueA
Suppose that, initially, QueueA contains N data items, and QueueB is empty.

Add semaphore operations (P and V) to the skeleton implementations of AtoB() and BtoA() so that the following synchronization requirements are satisfied:
1. dequeue() should never be run on an empty queue.
2. At most one thread at a time should be using each queue. For example, if one thread is running dequeue() on QueueA, no other thread should be running dequeue() or enqueue() on QueueA.
3. Items must be enqueued onto QueueB in the same order that they are dequeued from QueueA. Similarly, items must be enqueued onto QueueA in the same order that they are dequeued from QueueB.
4. Threads must never deadlock.

Do not use any synchronization primitives other than semaphores in your solution. Do not make any changes to the skeleton code other than inserting calls to semaphore operations.

(Skeleton implementations and declarations are provided to students; do not provide solutions in the exam text here.)

```json
{
  "problem_id": "6",
  "points": 8,
  "type": "Freeform",
  "tags": ["semaphores","concurrency","queues"],
  "answer": "Answer consists of adding appropriate P and V semaphore calls to the provided skeleton so that: P(Acount) before dequeue from A, P(Amutex) to protect QueueA operations, P(AtoBmutex) to enforce ordering among AtoB operations, V(Bcount) after enqueue to B; symmetrically for BtoA: P(Bcount), P(Bmutex), P(BtoAmutex), V(Acount) after enqueue to A, with proper mutex V calls and no deadlock. The exact code matches the intended solution sketch.",
  "llm_judge_instructions": "Award 4 points for a correct AtoB implementation that ensures safety (no dequeue on empty), mutual exclusion on QueueA, and ordering, and avoids deadlock. Award 4 points for a correct BtoA implementation that ensures safety, mutual exclusion on QueueB, and ordering, and avoids deadlock. Total 8 points."
}
```

---

## Question 7a [3 point(s)]

a. (3 total marks)Which of the following effects does a MIPS syscall instruction have when it is executed? (Note: we are interested only in the effects of this single instruction, not the effects of any code that runs after this instruction.) Circle all that apply.
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
  "tags": ["mips","syscall","kernel"],
  "answer": "the current value of the program counter is saved; a trap frame is saved; the processor switches to privileged execution mode; the value of the program counter is changed",
  "llm_judge_instructions": "Award 3 points if the student selects exactly the set: {the current value of the program counter is saved, a trap frame is saved, the processor switches to privileged execution mode, the value of the program counter is changed}. Otherwise award 0 points."
}
```

---

## Question 7b [2 point(s)]

b. (2 total marks)Neither threads that are in the ready state nor threads that are in the blocked state are running. What is the difference between these two states?

```json
{
  "problem_id": "7b",
  "points": 2,
  "type": "Freeform",
  "tags": ["scheduling","states"],
  "answer": "A ready thread is runnable and will run again as soon as the scheduler chooses it. A blocked thread will not become runnable again until some event wakes it up (e.g., a wchan wakeone or wakeall).",
  "llm_judge_instructions": "Award 1 point for stating that a ready thread is runnable and can be scheduled. Award 1 point for stating that a blocked thread is not runnable until woken by some event. Total 2 points."
}
```

---

## Question 7c [2 point(s)]

c. (2 total marks)Explain why disabling interrupts may not enforce mutual exclusion on a multi-processor machine.

```json
{
  "problem_id": "7c",
  "points": 2,
  "type": "Freeform",
  "tags": ["multiprocessor","mutex","interrupts"],
  "answer": "Disabling interrupts on one processor only protects that processor; another processor can still execute in the critical section, so mutual exclusion is not guaranteed on multicore systems.",
  "llm_judge_instructions": "Award 2 points for explaining that disabling interrupts on one CPU does not prevent other CPUs from entering the critical section, thus not guaranteeing mutual exclusion on multiprocessor systems."
}
```

---

## Question 7d [1 point(s)]

d. (1 total marks)If a thread avoids “holding and waiting”, then that thread will never be involved in a deadlock. True or false?

```json
{
  "problem_id": "7d",
  "points": 1,
  "type": "Freeform",
  "tags": ["deadlock","holding-and-wait"],
  "answer": "False. A thread could wait for a resource held by another thread that becomes part of a deadlock.",
  "llm_judge_instructions": "Award 1 point for answering 'False' and providing a brief explanation that avoiding hold-and-wait does not guarantee a thread will never be involved in a deadlock in all scenarios."
}
```

---

## Question 7e [1 point(s)]

e. (1 total marks)If all threads avoid “holding and waiting”, then no thread will ever be involved in a deadlock. True or false?

```json
{
  "problem_id": "7e",
  "points": 1,
  "type": "Freeform",
  "tags": ["deadlock","holding-and-wait"],
  "answer": "True.",
  "llm_judge_instructions": "Award 1 point for answering 'True' and optionally a brief justification that avoiding hold-and-wait removes one of the necessary conditions for deadlock."
}
```

---

## Question 7f [3 point(s)]

f. (3 total marks)We have identified three types of events that cause execution control to transfer from an application program to the kernel. What are those three types of events?

```json
{
  "problem_id": "7f",
  "points": 3,
  "type": "Freeform",
  "tags": ["kernel","events","system-calls"],
  "answer": "System calls, interrupts, and exceptions.",
  "llm_judge_instructions": "Award 1 point for each correctly named type among {system calls, interrupts, exceptions}. Total 3 points."
}
```

---

## Question 7g [2 point(s)]

g. (2 total marks)Suppose that a process P calls waitpid and blocks because the process it is waiting for is still running. At the time that P blocks, how many trap frames will be on P’s thread’s stacks, and which stack, or stacks, will those trap frames be found on? Briefly justify your answer.

```json
{
  "problem_id": "7g",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel","stack","trap-frame"],
  "answer": "One trap frame on P's thread's kernel stack, created when the thread switched to kernel mode to handle waitpid.",
  "llm_judge_instructions": "Award 2 points for stating there is one trap frame on the kernel stack and briefly justifying that it was created during kernel entry for waitpid."
}
```

---

## Question 7h [2 point(s)]

h. (2 total marks)For the same situation described in part (g), how many switch frames will be on P’s thread’s stacks, and which stack, or stacks, will those switch frames be found on? Briefly justify your answer.

```json
{
  "problem_id": "7h",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel","switch-frame"],
  "answer": "One switch frame on P's thread's kernel stack; created when P's thread blocked and the scheduler switched to another thread.",
  "llm_judge_instructions": "Award 2 points for identifying one switch frame on the kernel stack and explaining that it is created when the thread blocks and the scheduler switches context."
}
```