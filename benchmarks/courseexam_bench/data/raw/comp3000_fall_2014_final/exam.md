# COMP 3000A: Operating Systems

```json
{
  "exam_id": "comp3000_fall_2014_final",
  "test_paper_name": "COMP 3000A: Operating Systems",
  "course": "COMP 3000",
  "institution": "Carleton University",
  "year": 2014,
  "score_total": 25,
  "num_questions": 22
}
```

---

## Question 1 [1 point]

Each file has read, write, and execute permissions specified three times, e.g., a file may have
“rw-r–r–”. Why three times and not just once?

```json
{
  "problem_id": "1",
  "points": 1,
  "type": "Freeform",
  "tags": ["permissions", "unix"],
  "answer": "In UNIX the first set of permissions are for the file’s owner, the next set is for members of the file’s group, and the third is for everyone else.",
  "llm_judge_instructions": "Award 1.0 point for correctly identifying owner, group, and others. Award 0.5 points for identifying two of the three correctly. 0 points otherwise."
}
```

---

## Question 2 [1 point]

What is the kernel mechanism that allows a user to forcibly terminate a running process in UNIX? Illustrate with an example.

```json
{
  "problem_id": "2",
  "points": 1,
  "type": "Freeform",
  "tags": ["signals"],
  "answer": "You send a KILL or -9 signal to a process to forcibly terminate it. For example: kill -SIGKILL 547 or kill -9 547.",
  "llm_judge_instructions": "Award 1.0 point for mentioning SIGKILL (or -9) and giving an example command. Award 0.5 points for mentioning signals in general without specifying SIGKILL. 0 points otherwise."
}
```

---

## Question 3 [1 point]

If we have a system where virtual address 0x722B2104 mapped to physical address 0x16AB2104, what is the largest page size that could be used for this mapping? Explain briefly.

```json
{
  "problem_id": "3",
  "points": 1,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging"],
  "answer": "The largest page size is 2^23 bytes.",
  "llm_judge_instructions": "Award 1.0 point for stating 2^23 bytes as the largest page size. Award 0.5 points for a partial explanation that correctly describes comparing low-order bits or hex digits to find the common suffix, but require the final page size (2^23) for full credit."
}
```

---

## Question 4 [1 point]

Do pointers in userspace C programs contain virtual or physical addresses on Linux? Explain briefly.

```json
{
  "problem_id": "4",
  "points": 1,
  "type": "Freeform",
  "tags": ["pointers", "address-space"],
  "answer": "All pointers in userspace contain virtual addresses because userspace programs run in a virtual address space. Physical addresses are only accessible in supervisor/kernel mode.",
  "llm_judge_instructions": "Award 1.0 point for stating that userspace pointers are virtual addresses and briefly noting that physical addresses are accessible only in kernel/supervisor mode. Award 0.5 points for mentioning virtual addresses without the kernel-mode justification."
}
```

---

## Question 5 [1 point]

What data structure allows the kernel to determine when a process is accessing an invalid memory area?

```json
{
  "problem_id": "5",
  "points": 1,
  "type": "Freeform",
  "tags": ["memory-management"],
  "answer": "A process’s page table.",
  "llm_judge_instructions": "Award 1.0 point for naming the page table. 0 points otherwise."
}
```

---

## Question 6 [1 point]

In C, the function call stack is used to store three distinct kinds of values, only one of which is required to be there by the CPU. Which value is required to be there by the CPU?

```json
{
  "problem_id": "6",
  "points": 1,
  "type": "Freeform",
  "tags": ["call-stack"],
  "answer": "The return address.",
  "llm_judge_instructions": "Award 1.0 point for identifying the return address as required by the CPU. 0 points otherwise."
}
```

---

## Question 7 [1 point]

In a system with a 64-bit address space, does the physical address space have more than 64 bits, 64 bits exactly, or less than 64 bits? Explain.

```json
{
  "problem_id": "7",
  "points": 1,
  "type": "Freeform",
  "tags": ["address-space"],
  "answer": "Less than 64 bits, because physically addressable memory is limited by hardware; e.g., many systems use 48-bit physical addresses.",
  "llm_judge_instructions": "Award 1.0 point for stating that physical addresses are typically less than 64 bits with a brief hardware-based justification (for example, citing typical implementations like 48-bit physical addresses). 0.5 points for stating 'less than 64 bits' without justification."
}
```

---

## Question 8 [1 point]

Can concurrency primitives such as mutexes be implemented without the use of special instructions such as xchg on modern CPUs? In other words, can such concurrency primitives be written purely in C on current processors? Explain.

```json
{
  "problem_id": "8",
  "points": 1,
  "type": "Freeform",
  "tags": ["concurrency", "atomic-ops"],
  "answer": "Concurrency primitives generally require special atomic instructions (e.g., xchg, compare-and-swap) to ensure atomicity and proper memory synchronization across cores.",
  "llm_judge_instructions": "Award a total of 1.0 point as follows: 0.5 points for stating that special atomic instructions are required to implement correct concurrency primitives; 0.5 points for mentioning the need for memory synchronization/consistency across cores (e.g., cache coherence or memory barriers)."
}
```

---

## Question 9 [2 points]

A fork bomb can be as simple as “while (1) fork();”. Why are fork bombs so dangerous? Explain why a fork bomb can kill system performance (assuming a system that does not have built-in defenses against fork bomb-like attacks).

```json
{
  "problem_id": "9",
  "points": 2,
  "type": "Freeform",
  "tags": ["fork", "process-management"],
  "answer": "Fork bombs are dangerous because they create an unbounded number of processes. The scheduler must give CPU time to all processes, so legitimate processes receive very little CPU. The system can exhaust process table entries, making it impossible to start new processes or respond to the user.",
  "llm_judge_instructions": "Award 2.0 points total: 1.0 point for explaining unbounded process creation leading to CPU starvation (scheduler overload), and 1.0 point for explaining exhaustion of system resources (e.g., process table entries, memory) that prevents normal operation. Award up to 1.0 point for mentioning only one of these aspects with reasonable detail."
}
```

---

## Question 10 [2 points]

What is the relationship between function calls, system calls, and library calls?

```json
{
  "problem_id": "10",
  "points": 2,
  "type": "Freeform",
  "tags": ["system-calls", "library", "function-calls"],
  "answer": "Function calls and library calls occur within a process; system calls invoke kernel code and switch to supervisor mode. Library calls go to dynamically linked libraries; function calls are internal. System calls use mechanisms (e.g., a system call dispatcher) to enter the kernel, while library calls are just ordinary calls with possible indirection due to dynamic linking.",
  "llm_judge_instructions": "Award 2.0 points total: 1.0 point for distinguishing function/library calls inside a process from system calls that enter the kernel, and 1.0 point for mentioning the role of dynamic linking/indirection versus direct function calls (or other correct distinctions). Award up to 1.0 point for partially correct explanations that capture at least one of these distinctions."
}
```

---

## Question 11a [0.5 point]

What happens when you type a command at a shell prompt in UNIX that is not built in to the shell? Specifically: 1) what code does it run?

```json
{
  "problem_id": "11a",
  "points": 0.5,
  "type": "Freeform",
  "tags": ["shell"],
  "answer": "An external executable with the same name as the command runs in a new process.",
  "llm_judge_instructions": "Award 0.5 points for recognizing that an external executable is run in a new process. 0 points otherwise."
}
```

---

## Question 11b [0.5 point]

2) how does it find that code?

```json
{
  "problem_id": "11b",
  "points": 0.5,
  "type": "Freeform",
  "tags": ["shell"],
  "answer": "The shell searches for the named binary in the directories listed in the PATH environment variable.",
  "llm_judge_instructions": "Award 0.5 points for identifying PATH-based lookup. 0 points otherwise."
}
```

---

## Question 11c [1.0 point]

3) what system calls (if any) does the shell do (at minimum) in order to execute that command?

```json
{
  "problem_id": "11c",
  "points": 1.0,
  "type": "Freeform",
  "tags": ["shell"],
  "answer": "The shell forks a child process and then the child uses execve to run the named binary.",
  "llm_judge_instructions": "Award 1.0 point total: 0.5 points for mentioning fork and 0.5 points for mentioning execve. Award 0.5 points for describing one of them correctly (partial credit)."
}
```

---

## Question 12 [1 point]

Hard Disk Recovery: Your Linux computer’s hard disk is starting to produce errors and you do not have a current backup of the disk. Your old disk is 500Gb; you are replacing it with a 2Tb drive (2000 Gb). You have already purchased and installed the new disk in the computer and have installed a fresh copy of Linux onto it. The new hard drive is now /dev/sda, with everything in one partition in /dev/sda1, while the old hard drive is in /dev/sdb, with all of its data in /dev/sdb1. You boot from the first disk and the old, failing disk (/dev/sdb) is unmounted.

To make the files on /dev/sdb1 accessible in /mnt, what command should you run (as root)? Please give the full command.

```json
{
  "problem_id": "12",
  "points": 1,
  "type": "Freeform",
  "tags": ["linux", "disk-recovery"],
  "answer": "mount /dev/sdb1 /mnt",
  "llm_judge_instructions": "Award 1.0 point for the exact mount command: 'mount /dev/sdb1 /mnt'. 0 points otherwise."
}
```

---

## Question 13 [1 point]

When attempting to access files from the disk you find that the underlying filesystem has been heavily corrupted. So, you’d like to try and repair the damage. What command should you use to attempt to repair the filesystem on /dev/sdb1?

```json
{
  "problem_id": "13",
  "points": 1,
  "type": "Freeform",
  "tags": ["linux", "fsck"],
  "answer": "fsck /dev/sdb1 (or fsck.ext4 /dev/sdb1 depending on the filesystem)",
  "llm_judge_instructions": "Award 1.0 point for mentioning fsck with /dev/sdb1 as the target (fsck /dev/sdb1 or fsck.ext4 /dev/sdb1). Partial credit (0.5) for generic mention of filesystem repair tools without the device."
}
```

---

## Question 14 [1 point]

Before you attempt the repair a friend warns you that if the repair goes badly you may lose even more data from the disk. Thus you decide you want to copy the raw data from disk into a file first. What command could you use to make a bit-for-bit copy of /dev/sdb1 into the file /old-image?

```json
{
  "problem_id": "14",
  "points": 1,
  "type": "Freeform",
  "tags": ["linux", "disk-image"],
  "answer": "dd if=/dev/sdb1 of=/old-image",
  "llm_judge_instructions": "Award 1.0 point for the exact dd command: 'dd if=/dev/sdb1 of=/old-image'. 0 points otherwise."
}
```

---

## Question 15 [2 points]

You decide to use the rsync command to copy the files from /mnt to /old. Because the old disk is failing, you have to run rsync multiple times. You notice that each time rsync seems to pick up right where it left off: it doesn’t copy files that have been fully transferred but does continue to copy files that it was in the middle of copying.

How does rsync know which files to copy? And is it possible for rsync to make a mistake (to not copy a file that is in fact different between the two directories)?

```json
{
  "problem_id": "15",
  "points": 2,
  "type": "Freeform",
  "tags": ["rsync"],
  "answer": "Rsync compares file metadata (mod-time, size, etc.) and copies files whose metadata differs. By default, contents are not compared unless --checksum is used. Thus, if a file’s contents differ but metadata matches, rsync may skip it.",
  "llm_judge_instructions": "Award a total of 2.0 points as follows: 1.0 point for explaining that rsync primarily uses metadata (e.g., modification time and size) to decide whether to copy, 0.5 points for noting that --checksum forces content-based comparison, and 0.5 points for acknowledging that rsync can miss differences if metadata matches (unless checksum is used)."
}
```

---

## Question 16 [1 point]

We want to use an authentication agent-type architecture where one process will store and protect all of a user’s secrets. We know that ssh has a similar architecture but we don’t understand how various processes can find the authentication agent. How do processes know how to contact the authentication agent for the current user?

```json
{
  "problem_id": "16",
  "points": 1,
  "type": "Freeform",
  "tags": ["authentication", "agents"],
  "answer": "Processes read the environment variable, e.g., SSH_AUTH_SOCK, which tells them how to contact the agent.",
  "llm_judge_instructions": "Award 1.0 point for mentioning the environment variable (such as SSH_AUTH_SOCK) and explaining that it provides the address (socket) for contacting the agent. 0 points otherwise."
}
```

---

## Question 17 [1 point]

We’ve implemented a custom filesystem using FUSE. On some file operations our FUSE process crashes with a segmentation violation error. What sort of coding error is causing the segmentation violation?

```json
{
  "problem_id": "17",
  "points": 1,
  "type": "Freeform",
  "tags": ["fuse", "kernel-space"],
  "answer": "Dereferencing an invalid pointer, e.g., attempting to dereference a NULL pointer.",
  "llm_judge_instructions": "Award 1.0 point for identifying an invalid pointer dereference (e.g., NULL dereference or other invalid memory access) as the cause. Award 0.5 points for partial answers that mention NULL pointer or general invalid memory access without explicitly stating it causes a segfault."
}
```

---

## Question 18 [1 point]

When the FUSE process crashes the filesystem still is listed by the df command, even though no files can be accessed in it. How can you tell the kernel that our FUSE-based filesystem should no longer be accessible?

```json
{
  "problem_id": "18",
  "points": 1,
  "type": "Freeform",
  "tags": ["fuse", "mounts"],
  "answer": "fusermount -u <name-of-mountpoint>",
  "llm_judge_instructions": "Award 1.0 point for the command 'fusermount -u <mountpoint>' or equivalent unmount command that unmounts the FUSE mount. 0 points otherwise."
}
```

---

## Question 19 [1 point]

One of our new developers is saying that our filesystem will perform better if we implement it as a kernel module rather than using FUSE. What is one reason you would expect a kernel implementation of a filesystem to be faster than one implemented using FUSE?

```json
{
  "problem_id": "19",
  "points": 1,
  "type": "Freeform",
  "tags": ["filesystem", "kernel"],
  "answer": "A kernel implementation can be faster because it avoids a second context switch into the user-space process that handles the FUSE filesystem.",
  "llm_judge_instructions": "Award 1.0 point for mentioning reduced context switch or user/kernel transition overhead as the primary reason for the potential speedup. 0 points otherwise."
}
```

---

## Question 20 [2 points]

If the current buggy FUSE code is ported to a kernel module, would you expect it to still generate segmentation violations? Explain.

```json
{
  "problem_id": "20",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-module", "bugs"],
  "answer": "The same bad pointer dereferences would still be there, but in the kernel they wouldn’t generate user-space SIGSEGV. The kernel might produce Oops messages or panic, but signals like SIGSEGV are for processes. The kernel is not a process.",
  "llm_judge_instructions": "Award 2.0 points total: 1.0 point for explaining that kernel-space invalid memory accesses do not generate user-space SIGSEGV but can cause kernel Oops/panic or other kernel diagnostics, and 1.0 point for noting that the underlying bug (invalid pointer dereference) remains and will still cause failures in kernel mode. Award 1.0 point for a partial answer that states the bug remains without detailing kernel behavior."
}
```