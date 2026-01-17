# COMP 3000A Fall 2014 Final Exam

```json
{
  "exam_id": "comp3000_fall_2014_final",
  "test_paper_name": "COMP 3000A Fall 2014 Final Exam",
  "course": "COMP3000",
  "institution": "Carleton University",
  "year": 2014,
  "score_total": 25,
  "num_questions": 20
}
```

---

## Question 1 [1 point(s)]

{Question text ONLY - no answer, no solution in the text}

```json
{
  "problem_id": "1",
  "points": 1,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "In UNIX the first set of permissions are for the file's owner, the next set is for members of the file's group, and the third is for everyone else.",
  "llm_judge_instructions": "Award up to 1.0 point: 1.0 point if the response correctly names all three scopes (owner, group, others) and gives brief correct context; 0.5 points if exactly two scopes are correctly named; 0.25 points if exactly one scope is correctly named; 0.0 points if none are correct."
}
```

---

## Question 2 [1 point(s)]

What is the kernel mechanism that allows a user to forcibly terminate a running process in UNIX? Illustrate with an example.

```json
{
  "problem_id": "2",
  "points": 1,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "You send a signal such as SIGKILL (often via kill -SIGKILL <pid> or kill -9 <pid>) to forcibly terminate a process.",
  "llm_judge_instructions": "Award up to 1.0 point: 1.0 point for naming signal-based termination (e.g., SIGKILL/-9) and providing a correct example command; 0.5 points if the answer mentions signals but gives no correct example, or provides an example but does not mention signals explicitly; 0.0 points otherwise."
}
```

---

## Question 3 [1 point(s)]

If we have a system where virtual address 0x722B2104 mapped to physical address 0x16AB2104, what is the largest page size that could be used for this mapping? Explain briefly.

```json
{
  "problem_id": "3",
  "points": 1,
  "type": "Freeform",
  "tags": ["virtual-memory"],
  "answer": "2^23 bytes (the largest page size is determined by the number of identical low-order bits in the virtual and physical addresses; here the common low-order 23 bits imply a 2^23-byte page).",
  "llm_judge_instructions": "Award up to 1.0 point: 1.0 point for giving the correct largest page size (2^23 bytes) with brief correct reasoning; 0.5 points for correctly explaining the method (common low-order bits) but not providing the final numeric page size; 0.0 points otherwise."
}
```

---

## Question 4 [1 point(s)]

Do pointers in userspace C programs contain virtual or physical addresses on Linux? Explain briefly.

```json
{
  "problem_id": "4",
  "points": 1,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "They contain virtual addresses. User-space processes use a virtual address space; physical addresses are only directly used in kernel/supervisor mode.",
  "llm_judge_instructions": "Award up to 1.0 point: 1.0 point for stating that user-space pointers are virtual addresses and providing a brief correct justification (e.g., virtual address space and translation via page tables); 0.5 points for stating 'virtual' without adequate justification; 0.0 points otherwise."
}
```

---

## Question 5 [1 point(s)]

What data structure allows the kernel to determine when a process is accessing an invalid memory area?

```json
{
  "problem_id": "5",
  "points": 1,
  "type": "Freeform",
  "tags": ["memory-management"],
  "answer": "A process's page table.",
  "llm_judge_instructions": "Award 1.0 point for identifying the page table (or equivalent address-translation structure such as page tables/memory management unit entries). 0.0 points otherwise."
}
```

---

## Question 6 [1 point(s)]

In C, the function call stack is used to store three distinct kinds of values, only one of which is required to be there by the CPU. Which value is required to be there by the CPU?

```json
{
  "problem_id": "6",
  "points": 1,
  "type": "Freeform",
  "tags": ["programming-language","cpu-architecture"],
  "answer": "The return address.",
  "llm_judge_instructions": "Award 1.0 point for identifying the return address as the value required by the CPU; 0.0 points otherwise."
}
```

---

## Question 7 [1 point(s)]

In a system with a 64-bit address space, does the physical address space have more than 64 bits, 64 bits exactly, or less than 64 bits? Explain.

```json
{
  "problem_id": "7",
  "points": 1,
  "type": "Freeform",
  "tags": ["architectures"],
  "answer": "Typically less than 64 bits (for example many current systems use 48-bit or similar physical addresses).",
  "llm_judge_instructions": "Award up to 1.0 point: 1.0 point for stating the physical address space is typically less than 64 bits and giving a plausible example (e.g., 48-bit); 0.5 points for stating 'less than 64 bits' without an example; 0.0 points otherwise."
}
```

---

## Question 8 [1 point(s)]

Can concurrency primitive such as mutexes be implemented without the use of special instruction such as xchg on modern CPUs? In other words, can such concurrency primitives be written purely in C on current processors? Explain.

```json
{
  "problem_id": "8",
  "points": 1,
  "type": "Freeform",
  "tags": ["concurrency","cpu-architecture"],
  "answer": "No; on modern multi-core CPUs you need atomic instructions (e.g., xchg, cmpxchg, atomic builtins) to implement correct mutexes to avoid races across cores and ensure atomicity and memory ordering.",
  "llm_judge_instructions": "Award up to 1.0 point: 1.0 point for stating that atomic hardware instructions are required (mentioning examples like xchg or cmpxchg or atomic builtins) and explaining why (cross-core synchronization/memory ordering); 0.5 points for mentioning need for synchronization or atomicity without naming an instruction or clear reason; 0.0 points otherwise."
}
```

---

## Question 9 [2 point(s)]

A fork bomb can be as simple as “while (1) fork();”. Why are fork bombs so dangerous? Explain why a fork bomb can kill system performance (assuming a system that does not have built-in defenses against fork bomb-like attacks).

```json
{
  "problem_id": "9",
  "points": 2,
  "type": "Freeform",
  "tags": ["process-management"],
  "answer": "Fork bombs rapidly create an unbounded number of processes, exhausting process table entries and other resources. The scheduler must attempt to allocate CPU time across many processes, starving legitimate work; system limits (PID space, memory, file descriptors) can be exhausted, causing system-wide degradation.",
  "llm_judge_instructions": "Award up to 2.0 points: 1.0 point for explaining that a fork bomb creates an unbounded number of processes and depletes resources (process table entries, memory, etc.); 1.0 point for explaining the impact on scheduling and system performance (e.g., CPU time fragmentation, starvation of other processes, system instability). Partial credit proportional to coverage of these points; 0.0 points if neither aspect is addressed."
}
```

---

## Question 10 [2 point(s)]

What is the relationship between function calls, system calls, and library calls?

```json
{
  "problem_id": "10",
  "points": 2,
  "type": "Freeform",
  "tags": ["systems-call-models"],
  "answer": "Function calls and library calls execute within the process in user space; system calls transfer control to the kernel (supervisor mode) via the system call interface/dispatcher. Library calls are function calls provided by libraries; some library calls may invoke system calls internally.",
  "llm_judge_instructions": "Award up to 2.0 points: 1.0 point for correctly explaining that function/library calls run in user-space within the process; 1.0 point for correctly explaining that system calls transition into the kernel (supervisor mode) via a syscall interface/dispatcher and may involve a context switch or trap. Partial credit awarded if one of the two aspects is correctly explained."
}
```

---

## Question 11 [2 point(s)]

What happens when you type a command at a shell prompt in UNIX that is not built in to the shell? Specifically: 1) what code does it run, 2) how does it find that code, and 3) what system calls (if any) does the shell do (at minimum) in order to execute that command?

```json
{
  "problem_id": "11",
  "points": 2,
  "type": "Freeform",
  "tags": ["shell","process-management"],
  "answer": "The shell locates an executable file (by searching directories listed in the PATH environment variable) and runs that program in a new process. Typically the shell forks to create a child process and the child uses execve (or equivalent) to replace its image with the executable.",
  "llm_judge_instructions": "Award up to 2.0 points: 1.0 point for explaining that the shell searches PATH to locate an external executable and distinguishes it from builtins (naming PATH is sufficient); 1.0 point for explaining that the shell uses fork (to create a child) and execve (or equivalent) to run the command in the child process. Partial credit if only one of these two components is correctly explained (award 1.0 if fully correct for one component, 0.5 if partial)."
}
```

---

## Question 12 [1 point(s)]

Hard Disk Recovery:Your Linux computer’s hard disk is starting to produce errors and you do not have a current backup of the disk. Your old disk is 500Gb; you are replacing it with a 2Tb drive (2000 Gb). You have already purchased and installed the new disk in the computer and have installed a fresh copy of Linux onto it. The new hard drive is now /dev/sda, with everything in one partition in /dev/sda1, while the old hard drive is in /dev/sdb, with all of its data in /dev/sdb1. You boot from the first disk and the old, failing disk (/dev/sdb) is unmounted.

```json
{
  "problem_id": "12",
  "points": 1,
  "type": "Freeform",
  "tags": ["disk-recovery"],
  "answer": "Make a full image or copy of the failing disk before attempting repairs or repeated mounts (for example, use ddrescue to image /dev/sdb to another drive/file), or mount the filesystem read-only to inspect it. Avoid writing to the failing disk.",
  "llm_judge_instructions": "Award up to 1.0 point: 1.0 point for advising to image/backup the failing disk (e.g., ddrescue) or to mount it read-only to avoid further damage; 0.5 points for suggesting one of these actions without sufficient justification; 0.0 points otherwise."
}
```

---

## Question 13 [1 point(s)]

To make the files on /dev/sdb1 accessible in /mnt,  what command should you run (as root)? Please give the full command.

```json
{
  "problem_id": "13",
  "points": 1,
  "type": "Freeform",
  "tags": ["disk-recovery"],
  "answer": "mount /dev/sdb1 /mnt",
  "llm_judge_instructions": "Award 1.0 point for the exact command: mount /dev/sdb1 /mnt. 0.0 points for any other command or incorrect syntax."
}
```

---

## Question 14 [1 point(s)]

When attempting to access files from the disk you find that the underlying filesystem has been heavily corrupted. So, you’d like to try and repair the damage. What command should you use to attempt to repair the filesystem on /dev/sdb1?

```json
{
  "problem_id": "14",
  "points": 1,
  "type": "Freeform",
  "tags": ["disk-recovery"],
  "answer": "fsck /dev/sdb1 (or the appropriate fsck.<fstype> such as fsck.ext4 /dev/sdb1).",
  "llm_judge_instructions": "Award 1.0 point for recommending fsck (or a specific fsck.<fstype>) with the device (e.g., fsck /dev/sdb1 or fsck.ext4 /dev/sdb1). 0.0 points otherwise."
}
```

---

## Question 15 [2 point(s)]

You decide to use rsync to copy the files from /mnt to /old. Because the old disk is failing, you have to run rsync multiple times. You notice that each rsync seems to pick up right where it left off, in that it doesn’t copy files that have been fully transferred but does continue to copy files that it was in the middle of copying. How does rsync know which files to copy? And is it possible for rsync to make a mistake (to not copy a file that is in fact different between the two directories)?

```json
{
  "problem_id": "15",
  "points": 2,
  "type": "Freeform",
  "tags": ["file-sync","rsync"],
  "answer": "By default rsync decides whether to copy based on file metadata such as size and modification time; it will skip files whose metadata indicate they are unchanged. This means it can miss differences if metadata match but contents differ; using the --checksum option forces content checksumming at the cost of speed.",
  "llm_judge_instructions": "Award up to 2.0 points: 1.0 point for explaining that rsync uses metadata (size, mtime) to decide whether to copy; 1.0 point for noting that this can lead to missed differences if metadata match and for mentioning --checksum as a remedy. Partial credit (1.0) if only one of the two main points is correctly explained."
}
```

---

## Question 16 [1 point(s)]

We want to use an authentication agent-type architecture where one process will store and protect all of a user’s secrets. We know that ssh has a similar architecture but we don’t understand how various processes can find the authentication agent. How do processes know how to contact the authentication agent for the current user?

```json
{
  "problem_id": "16",
  "points": 1,
  "type": "Freeform",
  "tags": ["security","authentication"],
  "answer": "Processes locate the authentication agent via environment variables such as SSH_AUTH_SOCK that point to the agent's communication socket.",
  "llm_judge_instructions": "Award 1.0 point for mentioning environment variables (e.g., SSH_AUTH_SOCK) that indicate how to contact the agent. 0.0 points otherwise."
}
```

---

## Question 17 [1 point(s)]

We’ve implemented a custom filesystem using FUSE. On some file operations our FUSE process crashes with a segmentation violation error. What sort of coding error is causing the segmentation violation?

```json
{
  "problem_id": "17",
  "points": 1,
  "type": "Freeform",
  "tags": ["filesystem","fuse"],
  "answer": "Most likely dereferencing an invalid pointer (for example dereferencing NULL or an uninitialized pointer).",
  "llm_judge_instructions": "Award 1.0 point for identifying invalid pointer dereference (e.g., NULL or uninitialized pointer) as the likely cause. 0.0 points otherwise."
}
```

---

## Question 18 [1 point(s)]

When the FUSE process crashes the filesystem still is listed by the df command, even though no files can be accessed in it. How can you tell the kernel that our FUSE-based filesystem should no longer be accessible?

```json
{
  "problem_id": "18",
  "points": 1,
  "type": "Freeform",
  "tags": ["filesystem","fuse"],
  "answer": "fusermount -u <mountpoint>",
  "llm_judge_instructions": "Award 1.0 point for the correct command syntax to unmount the FUSE filesystem (e.g., fusermount -u <mountpoint>). 0.0 points otherwise."
}
```

---

## Question 19 [1 point(s)]

One of our new developers is saying that our filesystem will perform better if we implement it as a kernel module rather than using FUSE. What is one reason you would expect a kernel implementation of a filesystem to be faster than one implemented using FUSE?

```json
{
  "problem_id": "19",
  "points": 1,
  "type": "Freeform",
  "tags": ["filesystem","kernel"],
  "answer": "Kernel implementation avoids the user-space process context switches and extra IPC between kernel and FUSE daemon, reducing overhead.",
  "llm_judge_instructions": "Award 1.0 point for noting that kernel-space implementation avoids extra context switches/IPC overhead incurred by FUSE, leading to better performance. 0.0 points otherwise."
}
```

---

## Question 20 [2 point(s)]

If the current buggy FUSE code is ported to a kernel module, would you expect it to still generate segmentation violations? Explain.

```json
{
  "problem_id": "20",
  "points": 2,
  "type": "Freeform",
  "tags": ["filesystem","kernel"],
  "answer": "Yes, the same coding errors (e.g., bad pointer dereferences) would still exist; however, in kernel context they do not raise user-space signals like SIGSEGV. Instead they typically produce kernel oops messages or cause a panic, affecting the whole system.",
  "llm_judge_instructions": "Award up to 2.0 points: 1.0 point for stating that the underlying bugs (e.g., pointer dereferences) will still exist after porting; 1.0 point for explaining the difference in failure modes in kernel context (no SIGSEGV for kernel code; rather Oops/panic and broader system impact). Partial credit (1.0) if only one of these aspects is explained correctly."
}
```