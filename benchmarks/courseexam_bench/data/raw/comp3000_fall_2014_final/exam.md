# COMP 3000 Fall 2014 Final

```json
{
  "exam_id": "comp3000_fall_2014_final",
  "test_paper_name": "COMP 3000 Fall 2014 Final",
  "course": "COMP 3000",
  "institution": "University of Carleton",
  "year": 2014,
  "score_total": 25,
  "num_questions": 20
}
```

---

## Question 1 [1 point(s)]

Each file has read, write, and execute permissions specified three times, e.g., a file may have “rw-r–r–”. Why three times and not just once?

```json
{
  "problem_id": "1",
  "points": 1,
  "type": "Freeform",
  "tags": ["unix","permissions","file-system"],
  "answer": "In UNIX the first set of permissions are for the file’s owner, the next set is for members of the file’s group, and the third is for everyone else.",
  "llm_judge_instructions": "Award 1 point for correctly identifying the tripartite permission sets (owner, group, others)."
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
  "tags": ["unix","signals","process-management"],
  "answer": "You send a KILL signal (SIGKILL, e.g., kill -SIGKILL <pid> or kill -9 <pid>).",
  "llm_judge_instructions": "Award 1 point for identifying signal-based termination (e.g., SIGKILL) and 0 points otherwise."
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
  "tags": ["virtual-memory","paging"],
  "answer": "2^23 bytes (the largest page size is determined by the number of identical low-order bits; here the common suffix allows 2^23).",
  "llm_judge_instructions": "Award 1 point for citing the maximum page size determined by common low-order bits, specifically 2^23 in this example."
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
  "tags": ["userspace","virtual-memory","pointers"],
  "answer": "All pointers in userspace contain virtual addresses because userspace runs in its own virtual address space.",
  "llm_judge_instructions": "Award 1 point for stating pointers are virtual addresses and brief justification."
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
  "tags": ["virtual-memory","memory-management"],
  "answer": "The page table of the process.",
  "llm_judge_instructions": "Award 1 point for identifying the page table as the data structure used to validate memory access."
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
  "tags": ["c","call-stack"],
  "answer": "The return address.",
  "llm_judge_instructions": "Award 1 point for identifying the return address as the required value."
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
  "tags": ["virtual-memory","architecture"],
  "answer": "Less than 64 bits; for example, current systems often have 48-bit physical addresses (e.g., 256 TB).",
  "llm_judge_instructions": "Award 1 point for noting the physical address space is smaller than 64 bits and giving an example such as 48-bit."
}
```

---

## Question 8 [1 point(s)]

Can concurrency primitives such as mutexes be implemented without the use of special instructions such as xchg on modern CPUs? In other words, can such concurrency primitives be written purely in C on current processors? Explain.

```json
{
  "problem_id": "8",
  "points": 1,
  "type": "Freeform",
  "tags": ["concurrency","cpu-instructions"],
  "answer": "Concurrency primitives must use special instructions because of memory hierarchy and synchronization requirements (e.g., xchg helps synchronize between cores).",
  "llm_judge_instructions": "Award 1 point for recognizing the need for special instructions (like xchg) to ensure correct synchronization."
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
  "tags": ["process-management","fork"],
  "answer": "Fork bombs are dangerous because they can create an unbounded number of processes; this exhausts CPU, memory, and process table resources, starving legitimate processes and potentially preventing system actions like killing the fork bomb.",
  "llm_judge_instructions": "Award 2 points for noting unbounded process creation and impact on CPU time and system resources; partial credit for describing resource exhaustion."
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
  "tags": ["systems","abstraction"],
  "answer": "Function calls and library calls run in the user process; system calls invoke the kernel and switch to supervisor mode; library calls are calls to dynamically linked libraries (indirect via relocation) while function calls are to statically linked code.",
  "llm_judge_instructions": "Award 2 points for distinguishing user-space function/library calls from kernel-space system calls and noting dynamic vs static linking aspects."
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
  "tags": ["shell","external-command","process-management"],
  "answer": "The shell runs a separate executable with the same name as the command in a new process; it searches PATH for the binary; the shell forks to create a child and then uses execve to run the command.",
  "llm_judge_instructions": "Award 2 points for identifying external command execution via fork and execve and PATH lookup."
}
```

---

## Question 12 [1 point(s)]

Hard Disk Recovery: To make the files on /dev/sdb1 accessible in /mnt, what command should you run (as root)? Please give the full command.

```json
{
  "problem_id": "12",
  "points": 1,
  "type": "Freeform",
  "tags": ["disk-recovery","mount"],
  "answer": "mount /dev/sdb1 /mnt",
  "llm_judge_instructions": "Award 1 point for the exact mount command."
}
```

---

## Question 13 [1 point(s)]

Hard Disk Recovery: When attempting to access files from the disk you find that the underlying filesystem has been heavily corrupted. So, you’d like to try and repair the damage. What command should you use to attempt to repair the filesystem on /dev/sdb1?

```json
{
  "problem_id": "13",
  "points": 1,
  "type": "Freeform",
  "tags": ["disk-recovery","fsck"],
  "answer": "fsck or fsck.ext4 (e.g., fsck /dev/sdb1).",
  "llm_judge_instructions": "Award 1 point for recommending fsck on /dev/sdb1."
}
```

---

## Question 14 [1 point(s)]

Hard Disk Recovery: Before you attempt the repair a friend warns you that if the repair goes badly you may lose even more data from the disk. Thus you decide you want to copy the raw data from disk into a file first. What command could you use to make a bit-for-bit copy of /dev/sdb1 into the file /old-image?

```json
{
  "problem_id": "14",
  "points": 1,
  "type": "Freeform",
  "tags": ["disk-recovery","dd"],
  "answer": "dd if=/dev/sdb1 of=/old-image",
  "llm_judge_instructions": "Award 1 point for the dd command that copies raw data."
}
```

---

## Question 15 [2 point(s)]

You decide to use the rsync command to copy the files from /mnt to /old. Because the old disk is failing, you have to run rsync multiple times. You notice that each timer rsync seems to pick up right where it left off, in that it doesn’t copy files that have been fully transferred but does continue to copy files that it was in the middle of copying. How does rsync know which files to copy? And is it possible for rsync to make a mistake (to not copy a file that is in fact different between the two directories)?

```json
{
  "problem_id": "15",
  "points": 2,
  "type": "Freeform",
  "tags": ["rsync","file-synchronization","troubleshooting"],
  "answer": "Rsync compares file metadata (modification time, size, etc.) and copies only those with differences; by default it does not compare contents. It can miss updates if metadata matches; using --checksum compares contents and is slower.",
  "llm_judge_instructions": "Award 2 points for describing metadata-based synchronization and the potential for missing differences; optionally award extra for mentioning --checksum."
}
```

---

## Question 16 [1 point(s)]

We want to use an authentication agent-type architecture where one process will store and protect all of a user’s secrets. How do processes know how to contact the authentication agent for the current user?

```json
{
  "problem_id": "16",
  "points": 1,
  "type": "Freeform",
  "tags": ["security","authentication","environment"],
  "answer": "Processes locate the authentication agent via environment variables, e.g., SSH_AUTH_SOCK.",
  "llm_judge_instructions": "Award 1 point for identifying the environment variable (SSH_AUTH_SOCK) that provides the agent contact info."
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
  "tags": ["fuse","kernel-space","pointer-errors"],
  "answer": "Dereferencing an invalid pointer, e.g., attempting to dereference a NULL pointer.",
  "llm_judge_instructions": "Award 1 point for pointing to a null/invalid pointer dereference as the likely cause."
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
  "tags": ["fuse","unmount"],
  "answer": "fusermount -u <name-of-mountpoint>",
  "llm_judge_instructions": "Award 1 point for the correct unmount command."
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
  "tags": ["filesystem","kernel-module","performance"],
  "answer": "A kernel implementation can avoid an extra context switch into the user-space FUSE process, reducing overhead.",
  "llm_judge_instructions": "Award 1 point for mentioning reduced context switches or in-kernel execution benefits."
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
  "tags": ["fuse","kernel-space","segmentation-faults"],
  "answer": "The same bad pointer dereferences would still be present, but in the kernel they wouldn’t generate SIGSEGV signals; instead, they may produce Oops messages or panics.",
  "llm_judge_instructions": "Award 2 points for explaining that kernel context changes remove typical user-space signals, with possible kernel Oops/panics instead."
}
```