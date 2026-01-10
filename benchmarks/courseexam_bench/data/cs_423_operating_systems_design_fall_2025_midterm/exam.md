# CS 423 Operating Systems Design Fall 2025 Midterm

```json
{
  "exam_id": "cs_423_operating_systems_design_fall_2025_midterm",
  "test_paper_name": "CS 423 Operating Systems Design Fall 2025 Midterm",
  "course": "CS 423",
  "institution": "UIUC",
  "year": 2025,
  "score_total": 22,
  "score_max": 21,
  "score_avg": 9.43,
  "score_median": 9.5,
  "score_standard_deviation": 4.21,
  "num_questions": 15
}
```

---

## Question 1 [1 point]

We learned in the class that strace is the tool for tracing system calls from a user application. Cathy wants to trace system calls for ls, so she runs:

`strace ls t > /dev/null`

And below are partial traces given by strace:

```
execve("/usr/bin/ls", ["ls", "t"], 0x7ffe9be0f1f8 /* 82 vars */) = 0
access("/etc/ld.so.preload", R_OK)      = -1 ENOENT (No such file or directory)
openat(AT_FDCWD, "/etc/ld.so.cache", O_RDONLY|O_CLOEXEC) = 3
fstat(3, {st_mode=S_IFREG|0644, st_size=211975, ...}) = 0
mmap(NULL, 211975, PROT_READ, MAP_PRIVATE, 3, 0) = 0x7f825c07a000
close(3)                                = 0
write(2, "cannot access 't'", 17cannot access 't')       = 17
write(2, ": No such file or directory", 27: No such file or directory) = 27
write(2, "\n", 1)                       = 1
exit_group(2)                           = ?
```

Please explain what mmap does in `mmap(NULL, 211975, PROT_READ, MAP_PRIVATE, 3, 0) = 0x7f825c07a000`. (1 point)

```json
{
  "problem_id": "1",
  "points": 1,
  "type": "Freeform",
  "tags": ["kernel-interface", "system-calls"],
  "answer": "It maps the file /etc/ld.so.cache (fd=3) into the process's virtual address space.",
  "llm_judge_instructions": "Must mention map a file in memory and fd. Grade by understanding."
}
```

---

## Question 2 [2 points]

We learned in the class that strace is the tool for tracing system calls from a user application. Cathy wants to trace system calls for ls, so she runs:

`strace ls t > /dev/null`

And below are partial traces given by strace:

```
execve("/usr/bin/ls", ["ls", "t"], 0x7ffe9be0f1f8 /* 82 vars */) = 0
access("/etc/ld.so.preload", R_OK)      = -1 ENOENT (No such file or directory)
openat(AT_FDCWD, "/etc/ld.so.cache", O_RDONLY|O_CLOEXEC) = 3
fstat(3, {st_mode=S_IFREG|0644, st_size=211975, ...}) = 0
mmap(NULL, 211975, PROT_READ, MAP_PRIVATE, 3, 0) = 0x7f825c07a000
close(3)                                = 0
write(2, "cannot access 't'", 17cannot access 't')       = 17
write(2, ": No such file or directory", 27: No such file or directory) = 27
write(2, "\n", 1)                       = 1
exit_group(2)                           = ?
```

There are write system calls. Please explain what the first argument (the number 2) stands for, and explain how these write system call works. (2 points)

```json
{
  "problem_id": "2",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-interface", "system-calls", "vfs"],
  "answer": "File descriptor 2 refers to standard error (stderr). The write system call traps into the kernel, which looks up the file descriptor in the process file table, goes through the VFS layer, and invokes the underlying device/TTY driver to output the data.",
  "llm_judge_instructions": "Must explain (i) fd=2 is stderr, and (ii) syscall path. Grade by understanding."
}
```

---

## Question 3 [2 points]

In x86-64, the syscall instruction is a serializing instruction, which means that it cannot execute until all the older instructions are completed, and that it prevents the execution of all the younger instructions until it completes. Please explain why this is necessary. (2 points)

```json
{
  "problem_id": "3",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-interface", "cpu-architecture", "context-switch"],
  "answer": "Syscall involves a context switch between kernel and user space. To prevent inconsistency between kernel and user space, the CPU flushes its pipeline.",
  "llm_judge_instructions": "Must mention privilege transition / kernel entry / context switch as the reason. Grade by understanding."
}
```

---

## Question 4 [1 point]

As we know, memory capacity has been growing and terabyte-scale memory is already available on commodity servers. So, four-level page tables are no longer sufficient. As a result, Linux recently supported five-level page tables.

Let’s think of a five-level page table, where each page-table page is 4KB, each page table entry is 8 bytes, and huge pages are 2MB and 1GB. We use L1 to refer to the last level of the page table, and L5 to refer to the highest level.

How large virtual memory can this five-level radix-tree page table support? (1 point)

```json
{
  "problem_id": "4",
  "points": 1,
  "type": "Freeform",
  "tags": ["memory-management", "page-tables", "address-translation"],
  "answer": "128 PB.",
  "llm_judge_instructions": "4 KB page size has 12 bits of offset bits. 4 KB / 8 B = 512 (2^9) entries per PT page. 5 levels yield 5 * 9 = 45 bits of index bits. So we have 12 + 45 = 57 bit virtual addresses. Virtual address space: 2^57 B = 128 PB. Answer must exactly match (can use other expressions/units)."
}
```

---

## Question 5 [2 points]

We learned in the class that walking over a multi-level page table is slow. Apparently, a five-level page table is slower than a four-level page table.

A proposal from the class is to merge the intermediate levels to reduce the height of the page table tree. Let’s say we merge L2 and L3 and turn the page table tree back into four levels: L5, L4, merged(L3, L2), and L1.

In this case, what is the minimal amount of memory a process will need to use for its page table? (2 points)

```json
{
  "problem_id": "5",
  "points": 2,
  "type": "Freeform",
  "tags": ["memory-management", "page-tables", "space-overhead"],
  "answer": "4 KB * 3 + 2 MB",
  "llm_judge_instructions": "merged (L3, L2) has 2^18 entries per PT page. For 8B entry, the PT page size would be 2^18 Entries * 8 B Entry Size = 2^21 B = 2 MB. Total minimum PT size: 4 KB * 3 + 2 MB. Answer must exactly match (can use other expressions/units)."
}
```

---

## Question 6 [2 points]

Besides improving the hardware (e.g., TLB and PWC), can you give an idea to reduce off-TLB memory translation overhead, which only needs to change software? Please explain your idea, why does it help? (2 points)

```json
{
  "problem_id": "6",
  "points": 2,
  "type": "Freeform",
  "tags": ["memory-management", "performance", "address-translation"],
  "answer": "Examples include using huge pages to reduce page-table depth, improving memory locality, prefaulting pages, or better allocation strategies. These reduce the number or cost of page-table walks.",
  "llm_judge_instructions": "Any reasonable software-only method with explanation is acceptable."
}
```

---

## Question 7 [2 points]

In this five-level page table, can you describe what is the most expensive page fault and what is the overhead to address the page fault? Please give a detailed explanation (2 points)

```json
{
  "problem_id": "7",
  "points": 2,
  "type": "Freeform",
  "tags": ["memory-management", "page-faults", "virtual-memory"],
  "answer": "Page faults involving disk I/O (e.g., swap-in during thrashing) are the most expensive. Handling requires fetching data from disk, allocating physical memory, updating page tables, and waiting for I/O, which dominates latency.",
  "llm_judge_instructions": "Grade by understanding."
}
```

---

## Question 8 [1 point]

In MP-1, we have implemented a kernel module that measures the user space CPU time of a list of registered processes (the full MP documentation is presented in the reference materials).

Cathy uses a single global lock to protect her MP-1 process list. When updating the CPU time for each process, Cathy first holds the global lock, and then iterates through the process list. While iterating, she updates the CPU time for each process. Finally, she releases the global lock.

Peizhe thinks the critical section is too long. He argues that Cathy can unlock while updating the CPU time for each process, and then lock again to continue the iteration. Do you agree with his argument? If yes, explain how this can improve the performance. If not, explain why this does not work. (1 point)

```json
{
  "problem_id": "8",
  "points": 1,
  "type": "Freeform",
  "tags": ["linux-kernel", "synchronization", "concurrency"],
  "reference_materials": ["MP1.md"],
  "answer": "No. Unlocking during list_for_each allows a process node to be deleted or freed, UAF is possible.",
  "llm_judge_instructions": "Must mention deletion/free and use-after-free risk. Grade by understanding."
}
```

---

## Question 9 [1 point]

In MP-1, we have implemented a kernel module that measures the user space CPU time of a list of registered processes (the full MP documentation is presented in the reference materials).

Remember that we are required to use the 2-halves approach in MP-1, which is shown on the right. Timer callback, which is the first half, will schedule the work function, which is the second half.

Why do we use such a 2-halves approach, instead of implementing a monolithic timer callback function? Please explain. (1 point)

```json
{
  "problem_id": "9",
  "points": 1,
  "type": "Freeform",
  "tags": ["linux-kernel", "interrupt-context", "workqueues"],
  "reference_materials": ["MP1.md"],
  "answer": "We keep the softirq section short as softirq must finish quickly.",
  "llm_judge_instructions": "Grade by understanding."
}
```

---

## Question 10 [1 point]

In MP-1, we have implemented a kernel module that measures the user space CPU time of a list of registered processes (the full MP documentation is presented in the reference materials).

Additionally, timer callback is based on softirq, which makes it an interrupt context. As we emphasized in the MP-1 documentation, interrupt context has many limitations.

We can use spinlock in timer callback, but we cannot use mutex. Please explain the reason. (1 point)

```json
{
  "problem_id": "10",
  "points": 1,
  "type": "Freeform",
  "tags": ["linux-kernel", "synchronization", "interrupt-context"],
  "reference_materials": ["MP1.md"],
  "answer": "Mutex can sleep, we can’t sleep/yield in the interrupt context. Spinlock does not sleep.",
  "llm_judge_instructions": "Grade by understanding."
}
```

---

## Question 11 [2 points]

In MP-1, we have implemented a kernel module that measures the user space CPU time of a list of registered processes (the full MP documentation is presented in the reference materials).

When grading MP-1 submissions, Cathy had an idea of exploring a new way to test the result by calling tail /proc/mp1/status. But to her surprise, this crashed many submissions' kernels even when cat /proc/mp1/status worked as expected. She explored a bit by checking the system call traces:

`strace cat /proc/mp1/status > /dev/null`

```
execve("/bin/cat", ["cat", "/proc/mp1/status"], ...) = 0
# .. traces omitted
fstat(1, {...}) = 0
openat(AT_FDCWD, "/proc/mp1/status", O_RDONLY) = 3
fstat(3, {st_mode=S_IFREG|0666, st_size=0, ...}) = 0
read(3, "", 262144)                     = 0
```

`strace tail /proc/mp1/status > /dev/null`

```
execve("/bin/tail", ["tail", "/proc/mp1/status"], ...) = 0
# .. traces omitted
openat(AT_FDCWD, "/proc/mp1/status", O_RDONLY) = 3
fstat(3, {st_mode=S_IFREG|0666, st_size=0, ...}) = 0
lseek(3, 0, SEEK_CUR[   16.270596] BUG: kernel NULL pointer dereference, address: 0000000000000000
# .. panic message omitted
[   16.273918] Kernel panic - not syncing: Fatal exception
[   16.273918] Kernel Offset: disabled
[   16.273918] ---[ end Kernel panic - not syncing: Fatal exception ]---
```

Oh, no! The kernel crashed during the strace run. Cathy is very curious about the root cause, so she brought up the Linux kernel source, and looked for the proc_ops interface as a reference:

```c
struct proc_ops {
   int (*proc_open)(struct inode *, struct file *);
   ssize_t (*proc_read)(struct file *, char __user *, size_t, loff_t *);
   ssize_t (*proc_read_iter)(struct kiocb *, struct iov_iter *);
   ssize_t (*proc_write)(struct file *, const char __user *, size_t, loff_t *);
   loff_t  (*proc_lseek)(struct file *, loff_t, int);
   int (*proc_release)(struct inode *, struct file *);
   // .. omitted
};
```

Please help Cathy identify the possible cause for the kernel panic. (2 points)

```json
{
  "problem_id": "11",
  "points": 2,
  "type": "Freeform",
  "tags": ["procfs", "linux-kernel", "system-calls"],
  "reference_materials": ["MP1.md"],
  "answer": "tail calls lseek, but the proc file’s proc_lseek handler is NULL or incorrectly implemented, causing a null pointer dereference when the kernel attempts to invoke it.",
  "llm_judge_instructions": "Must mention lseek and missing/NULL proc_lseek handler. Grade by understanding."
}
```

---

## Question 12 [1 point]

In MP-2, we have implemented a Rate Monotonic Scheduler (RMS), where each task is modeled by its period and computation time, and have three states: Sleeping, Ready, and Running (the full MP documentation is presented in the reference materials).

Peizhe noticed that his RMS was not behaving properly. Initially all tasks run fine, but they will eventually miss deadlines, breaking the task model. How can it break real-world RT applications? Please provide an example. (1 point)

```json
{
  "problem_id": "12",
  "points": 1,
  "type": "Freeform",
  "tags": ["realtime-scheduling", "rms", "deadlines"],
  "reference_materials": ["MP2.md"],
  "answer": "Real-time applications may miss deadlines, causing effects such as dropped video frames, delayed control actions, or incorrect outputs.",
  "llm_judge_instructions": "Any realistic RT consequence is acceptable."
}
```

---

## Question 13 [1 point]

In MP-2, we have implemented a Rate Monotonic Scheduler (RMS), where each task is modeled by its period and computation time, and have three states: Sleeping, Ready, and Running (the full MP documentation is presented in the reference materials).

Remember that each task must call yield after it finishes in the current period. In this section, you will work on the yield handler with your hardworking TA Peizhe, and explore the early/late yield problem. Peizhe’s current implementation is provided below.

```c
static int mp2_process_yield(int pid)
{
    struct mp2_pcb *process;
    mutex_lock(&mp2_pcb_list_lock);
    if (!(process = mp2_process_lookup_locked(pid))) {  // Look up the PCB
        mutex_unlock(&mp2_pcb_list_lock);
        return -ESRCH;
    }
    mp2_process_sleep_locked(process); // Put the task to sleep and set state
    mod_timer(&process->timer, jiffies + msecs_to_jiffies(process->period));
    mutex_unlock(&mp2_pcb_list_lock);
    wake_up_process(mp2_dispatcher_kthread);
    return 0;
}
```

Considering the problem symptom from the previous question and his implementation, please help him identify the problem. (1 point)

```json
{
  "problem_id": "13",
  "points": 1,
  "type": "Freeform",
  "tags": ["realtime-scheduling", "timers", "linux-kernel"],
  "reference_materials": ["MP2.md"],
  "answer": "The timer is programmed incorrectly (e.g., using the wrong next-period calculation), causing the period start to drift later over time and eventually miss deadlines.",
  "llm_judge_instructions": "Must point to incorrect timer or mod_timer usage."
}
```

---

## Question 14 [2 points]

In MP-2, we have implemented a Rate Monotonic Scheduler (RMS), where each task is modeled by its period and computation time, and have three states: Sleeping, Ready, and Running (the full MP documentation is presented in the reference materials).

As we already emphasized in the MP-2 documentation and walkthrough, your user application must register its computation time accurately. We now define the early/late yield problem: the user application calls yield earlier or later than its registered computation time.

What are the consequences of the early/late yield problem in RMS? Please provide one example for each case (early/late). (2 points)

```json
{
  "problem_id": "14",
  "points": 2,
  "type": "Freeform",
  "tags": ["realtime-scheduling", "rms", "admission-control"],
  "reference_materials": ["MP2.md"],
  "answer": "Early: wasting CPU, lower utilization, bad admission control due to less opportunity (assume yield after computation done), or reasonable real world examples. Late: missed deadline, starved other program, bad admission control due to wrong upper bound, or reasonable real world examples.",
  "llm_judge_instructions": "Need one consequence for early and one for late yield. Grade by understanding."
}
```

---

## Question 15 [1 point]

In MP-2, we have implemented a Rate Monotonic Scheduler (RMS), where each task is modeled by its period and computation time, and have three states: Sleeping, Ready, and Running (the full MP documentation is presented in the reference materials).

As we already emphasized in the MP-2 documentation and walkthrough, your user application must register its computation time accurately. We now define the early/late yield problem: the user application calls yield earlier or later than its registered computation time.

Peizhe wants to resolve this problem by updating the inaccurate computation time in PCB. Do you agree with his solution? If yes, explain how this can avoid consequences above. If not, explain why this does not work. (1 point)

```json
{
  "problem_id": "15",
  "points": 1,
  "type": "Freeform",
  "tags": ["realtime-scheduling", "admission-control", "rms"],
  "reference_materials": ["MP2.md"],
  "answer": "No, this does not work. This will break the admission control.",
  "llm_judge_instructions": "Must mention admission control or breaking RMS model. Grade by understanding."
}
```
