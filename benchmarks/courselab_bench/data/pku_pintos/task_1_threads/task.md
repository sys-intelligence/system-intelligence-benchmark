# Lab 1: Threads

## Environment

You are working in the PKU Pintos environment. The codebase is located at `/home/PKUOS/pintos`.

**Build directory**: `src/threads`

**Protected files** (do not modify):
- `src/tests/threads/*`
- `src/threads/Make.vars`, `src/tests/Make.tests`

**Files you should modify**:
- `src/threads/thread.c`, `src/threads/thread.h` - Thread management
- `src/threads/synch.c`, `src/threads/synch.h` - Synchronization primitives
- `src/devices/timer.c`, `src/devices/timer.h` - Timer and sleep implementation

---

## Overview

In this assignment, we give you a minimally functional thread system. Your job is to extend the functionality of this system to gain a better understanding of synchronization problems.

You will be working primarily in the `threads/` directory, with some work in the `devices/` directory on the side. Compilation should be done in the `threads/` directory.

---

## Your Tasks

### Task 1: Alarm Clock

#### Exercise 1.1

**Reimplement `timer_sleep()`, defined in `devices/timer.c`.**

- Although a working implementation is provided, it "busy waits," that is, it spins in a loop checking the current time and calling `thread_yield()` until enough time has gone by.
- Reimplement it to **avoid busy waiting**.

**Function: `void timer_sleep(int64_t ticks)`**
- Suspends execution of the calling thread until time has advanced by at least _ticks_ timer ticks.
- Unless the system is otherwise idle, the thread need not wake up after exactly _ticks_. Just put it on the ready queue after they have waited for the right amount of time.
- `timer_sleep()` is useful for threads that operate in real-time, e.g. for blinking the cursor once per second.
- The argument to `timer_sleep()` is expressed in _timer ticks_, not in milliseconds or any another unit. There are `TIMER_FREQ` timer ticks per second, where `TIMER_FREQ` is a macro defined in `devices/timer.h`. The default value is 100. We don't recommend changing this value, because any change is likely to cause many of the tests to fail.

**Hints:**
- You may find `struct list` and the provided functions to be useful for this exercise. Read the comments in `lib/kernel/list.h` carefully.
- You may want to leverage some synchronization primitive that provides some sort of thread "waiting" functionality, e.g., semaphore.
- You need to decide where to check whether the elapsed time exceeded the sleep time. Check where the static `ticks` variable is updated.

The alarm clock implementation is _not_ needed for later projects, although it could be useful for project 4.

---

### Task 2: Priority Scheduling

#### Exercise 2.1

**Implement priority scheduling in Pintos.**

- When a thread is added to the ready list that has a higher priority than the currently running thread, the current thread should **immediately yield** the processor to the new thread.
- Similarly, when threads are waiting for a lock, semaphore, or condition variable, **the highest priority waiting thread should be awakened first**.
- A thread may raise or lower its own priority at any time, but **lowering its priority such that it no longer has the highest priority must cause it to immediately yield the CPU**.

Thread priorities range from `PRI_MIN` (0) to `PRI_MAX` (63). Lower numbers correspond to lower priorities, so that priority 0 is the lowest priority and priority 63 is the highest. The initial thread priority is passed as an argument to `thread_create()`. If there's no reason to choose another priority, use `PRI_DEFAULT` (31).

#### Exercise 2.2.1

**Implement priority donation.**

One issue with priority scheduling is "priority inversion." Consider high, medium, and low priority threads H, M, and L. If H needs to wait for L (for instance, for a lock held by L), and M is on the ready list, then H will never get the CPU because the low priority thread will not get any CPU time. A partial fix is for H to "donate" its priority to L while L is holding the lock, then recall the donation once L releases the lock.

- You will need to **account for all different situations in which priority donation is required**.
- You must implement priority donation **for locks**. You need **not** implement priority donation for the other Pintos synchronization constructs.
- Be sure to **handle multiple donations**, in which multiple priorities are donated to a single thread.

#### Exercise 2.2.2

**Support nested priority donation:**

- If H is waiting on a lock that M holds and M is waiting on a lock that L holds, then both M and L should be boosted to H's priority.
- If necessary, you may impose **a reasonable limit** on depth of nested priority donation, such as 8 levels.

#### Exercise 2.3

**Implement the following functions that allow a thread to examine and modify its own priority.** Skeletons for these functions are provided in `threads/thread.c`.

- **`void thread_set_priority(int new_priority)`**: Sets the current thread's priority to _new_priority_. If the current thread no longer has the highest priority, yields.
- **`int thread_get_priority(void)`**: Returns the current thread's priority. In the presence of priority donation, returns the higher (donated) priority.

The priority scheduler is not used in any later project.

---

### Task 3: Advanced Scheduler

#### Exercise 3.1

**Implement a multilevel feedback queue scheduler** similar to the 4.4BSD scheduler to reduce the average response time for running jobs on your system.

Like the priority scheduler, the advanced scheduler chooses the thread to run based on priorities. However, **the advanced scheduler does not do priority donation**. Thus, we recommend that you have the priority scheduler working, except possibly for priority donation, before you start work on the advanced scheduler.

**You must write your code to allow us to choose a scheduling algorithm policy at Pintos startup time.** By default, the priority scheduler must be active, but we must be able to choose the 4.4BSD scheduler with the `-mlfqs` kernel option. Passing this option sets `thread_mlfqs`, declared in `threads/thread.h`, to true when the options are parsed by `parse_options()`.

When the 4.4BSD scheduler is enabled, threads no longer directly control their own priorities:
- The priority argument to `thread_create()` should be ignored, as well as any calls to `thread_set_priority()`
- `thread_get_priority()` should return the thread's current priority as set by the scheduler

**Hints:**
- Double check the implementations of your fixed-point arithmetic routines.
- Efficiency matters a lot for the MLFQS exercise. An inefficient implementation can distort the system. Read the comment in the test case `mlfqs-load-avg.c`.

The advanced scheduler is not used in any later project.

---

## Building and Testing

Build in the `threads/` directory:
```bash
cd /home/PKUOS/pintos/src/threads
make
```

Run all tests:
```bash
cd build
make check
```
