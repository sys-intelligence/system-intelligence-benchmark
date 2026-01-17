# COMP 3000B: Operating Systems

```json
{
  "exam_id": "comp3000_winter_2020_final",
  "test_paper_name": "COMP 3000B: Operating Systems",
  "course": "COMP 3000",
  "institution": "Carleton University",
  "year": 2020,
  "score_total": 60,
  "num_questions": 29
}
```

---

## Question 1 [2 point(s)]

When you interact with bash (via ssh or a graphical terminal) what file does bash read from in order to obtain user input? Is this file a regular file? Explain briefly.

```json
{
  "problem_id": "1",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "bash reads from a numbered file in /dev/pts (e.g., /dev/pts/0) to obtain user input. This is a character device, not a regular file.",
  "llm_judge_instructions": "Award full credit for identifying that bash reads from a /dev/pts device (a pseudoterminal) and that it is a character device, not a regular file."
}
```

---

## Question 2 [1 point(s)]

When you type the command ls > ls.log at a bash shell prompt, what process opens the file ls.log for writing, bash, ls, or another?

```json
{
  "problem_id": "2",
  "points": 1,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "bash",
  "llm_judge_instructions": "Award full credit if the answer is bash."
}
```

---

## Question 3 [2 point(s)]

When you typels -la at abashprompt,  what system call does bash use to receive user input? What system call does bash use to pass the -la argument to ls?

```json
{
  "problem_id": "3",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "read, execve",
  "llm_judge_instructions": "Award full credit for identifying the read system call for input and execve for executing ls with arguments."
}
```

---

## Question 4 [3 point(s)]

What system calls do the following C library functions make (on Ubuntu 18.04)? Note they may generate none, one, or multiple system calls. (a) fgets, (b) ioctl, (c) snprintf.

```json
{
  "problem_id": "4",
  "points": 3,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "a) read, b) ioctl, c) none",
  "llm_judge_instructions": "Award full credit for listing: (a) read, (b) ioctl, (c) none."
}
```

---

## Question 5 [2 point(s)]

Process A creates a child process B to open and write data to a file (and then terminate). What is the standard UNIX mechanism that allows B to inform A that the write to the file failed?  Explain, indicating how the error message would be sent and received.

```json
{
  "problem_id": "5",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "B calls exit with a return code indicating failure. A calls wait to get B’s exit code.",
  "llm_judge_instructions": "Award full credit for describing that the child can signal failure via exit status and the parent can retrieve it via wait."
}
```

---

## Question 6 [2 point(s)]

If you decided you didn’t want to run any pre-installed binaries and instead just wanted to run your own versions when you type in commands at a shell prompt, how could you do this? Would this change prevent other users of the system from using system binaries? Explain briefly.

```json
{
  "problem_id": "6",
 "points": 2,
 "type": "Freeform",
 "tags": ["operating-systems"],
 "answer": "You would change your PATH environment variable (by changing your shell configuration files, e.g., .bashrc, .bashprofile, .profile) to only list your directories, excluding /bin, /usr/bin, etc. This change wouldn’t affect any other users on the system.",
 "llm_judge_instructions": "Award full credit for describing updating PATH to prioritize user-owned binaries and noting it does not prevent other users from using system binaries."
}
```

---

## Question 7 [2 point(s)]

If a sleeping process receives a signal, will the signal handler run immediately or will it run after the sleep finishes? Explain briefly, giving evidence for your answer.

```json
{
  "problem_id": "7",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "The signal handler runs immediately, and then the sleep system call returns early (unless SA_RESTART is set, which may restart the sleep).",
  "llm_judge_instructions": "Award full credit for stating that the signal is delivered immediately and can interrupt the sleep; mention SA_RESTART caveat as applicable."
}
```

---

## Question 8 [2 point(s)]

SIGPIPE is sent to process to indicate a broken pipe, i.e., a write to a pipe that has no readers (but did previously). Alice, upon learning about SIGPIPE, says this is stupid, because the write would just return an error. Bob replies that SIGPIPE is useful just like SIGCHLD is. Is Alice right or is Bob? Explain how the signals are similar and a situation when SIGPIPE would be useful.

```json
{
  "problem_id": "8",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "The key benefit of SIGPIPE is informing a process that a pipe is broken even if it isn’t in the middle of doing a write. In producer/consumer scenarios, SIGPIPE can immediately alert the producer to the broken consumer, allowing prompt handling (or termination). This is similar to SIGCHLD notifying a parent when a child terminates, whereas wait introduces delay.",
  "llm_judge_instructions": "Award full credit for explaining SIGPIPE's immediate notification role and its usefulness in broken-pipe scenarios, analogous to SIGCHLD notification."
}
```

---

## Question 9 [2 point(s)]

If a process has a uid=1000, euid=1000, gid=1021, and egid=1021, what files can it read on the system? Why?

```json
{
  "problem_id": "9",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "The process can read files owned by uid 1000 with owner read bit set, files with group 1021 and with group read bit set, and any files not owned by 1021 and not with group 1021 that have the other read bit set. Directory paths must be readable/executable for the relevant owner/group/other. Access checks consider owner, then group, then other.",
  "llm_judge_instructions": "Award full credit for describing UNIX permission checks across user (owner), group, and other, and noting directory traversal requirements."
}
```

---

## Question 10 [2 point(s)]

With ssh, what is the purpose of the id_rsa file? What about id_rsa.pub file? What do they contain, and how are they used?

```json
{
  "problem_id": "10",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "The id_rsa file contains the user's private key, and id_rsa.pub contains the public key. They are used to authenticate to a remote system by placing the contents of id_rsa.pub in the remote system’s authorized_keys file.",
  "llm_judge_instructions": "Award full credit for correctly describing private vs public key roles and the use in SSH authentication."
}
```

---

## Question 11 [2 point(s)]

In a filesystem, can two files share the same inode? Explain briefly.

```json
{
  "problem_id": "11",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "Yes. Two filenames can be hard links to the same inode; they are different directory entries pointing to the same file contents.",
  "llm_judge_instructions": "Award full credit for describing hard links and the inode-sharing concept."
}
```

---

## Question 12 [2 point(s)]

Can you easily recover from erasing the primary and all backup superblocks of an ext4 filesystem? Explain why or why not.

```json
{
  "problem_id": "12",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "No. The primary and backup superblocks are essential for mounting. Without them, recovery requires reconstructing the superblock parameters or forensic data recovery; it is non-trivial.",
  "llm_judge_instructions": "Award full credit for recognizing the importance of superblocks and the difficulty of recovery."
}
```

---

## Question 13 [1 point(s)]

If you want the standard output of one program to be fed to the standard input of another program directly (without storing any data on disk), how could you do this without using the | operator? Explain with a short example.

```json
{
  "problem_id": "13",
  "points": 1,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "Create a named pipe (FIFO) and redirect programs to use it for stdout/stdin (e.g., mkfifo mypipe; (ls > mypipe &); wc < mypipe).",
  "llm_judge_instructions": "Award full credit for describing a named pipe method to connect program I/O without intermediate disk storage."
}
```

---

## Question 14 [2 point(s)]

Below is an implementaiton ofsem wait(). Does this version cause the process to sleep while waiting for the lock to be freed? Do you expect this implementation to work reliably in practice? Explain briefly.

```c
void sem_wait(int *lock)
{
  while (*lock == 0) {
    /*
    *wait
    */
  }
  *lock = 0;
}
```

```json
{
  "problem_id": "14",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "This version busy-waits; it does not sleep while waiting for the lock. It will not work reliably in practice due to a race between checking *lock and clearing it, so another process could modify the lock between the check and the assignment.",
  "llm_judge_instructions": "Award full credit for identifying busy-waiting and the race condition; note that proper atomic operations or sleeping synchronization are required."
}
```

---

## Question 15 [2 point(s)]

From an API perspective, which is simpler to create, a thread or a process? Which do you think requires more work on the kernel’s part? Explain briefly.

```json
{
  "problem_id": "15",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "A process is simpler to create via API (fork) than a thread (pthread_create). The kernel does more work for processes because it must copy the (logical) address space; threads share the address space, requiring less kernel work.",
  "llm_judge_instructions": "Award full credit for comparing fork vs pthread_create and describing kernel work differences."
}
```

---

## Question 16 [2 point(s)]

How could you add support for lseek operations to a character device module? Specifically, what function(s) would you add, and how could you make sure those functions were called at the right time?

```json
{
  "problem_id": "16",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "Add an llseek function (e.g., mymodule_llseek) with the same signature as lseek, register it in the file_operations structure (e.g., via .llseek), so the kernel calls it when a process uses lseek on the device.",
  "llm_judge_instructions": "Award full credit for indicating adding an llseek handler and wiring it in via struct file_operations."
}
```

---

## Question 17 [2 point(s)]

What is the difference between a process’s uid and euid? Specifically, what does the kernel use each for?

```json
{
  "problem_id": "17",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "uid identifies process ownership for STOP/KILL permissions; euid determines what resources the process can access (e.g., file access) by comparing against file owners.",
  "llm_judge_instructions": "Award full credit for distinguishing owner vs effective user IDs and their use in permissions."
}
```

---

## Question 18 [2 point(s)]

Does the kernel know the names of the groups a user belongs to? How do you know?

```json
{
  "problem_id": "18",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "The kernel does not know the human-readable group names; it only knows gids. Changing active groups is done via setgid-related mechanisms (e.g., newgrp) which can affect the process's effective gid.",
  "llm_judge_instructions": "Award full credit for noting that the kernel tracks gids, not group names, and how groups are changed."
}
```

---

## Question 19 [2 point(s)]

When a process mmap’s a file, can it (mostly) control where the file will be placed in virtual memory? What about physical memory?

```json
{
  "problem_id": "19",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "A process can largely control the virtual address where the mapping appears. The kernel largely controls which physical memory is used, so the process has little control over the physical placement.",
  "llm_judge_instructions": "Award full credit for distinguishing virtual address control by the process from limited control over physical memory placement."
}
```

---

## Question 20 [2 point(s)]

Can two processes have data at the same virtual address?  What about at the same physical address? Explain.

```json
{
  "problem_id": "20",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "Two processes can have the same virtual address, but they reference different data (separate address spaces). They can share data at the same physical address via shared memory or mmap of the same file; otherwise, physical addresses are unique per process.",
  "llm_judge_instructions": "Award full credit for explaining virtual address space isolation and shared memory/physical address sharing."
}
```

---

## Question 21 [3 point(s)]

For each of the following, state and explain whether they support lseek operations always, sometimes, or never: regular files, pipes, character devices

```json
{
  "problem_id": "21",
  "points": 3,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "Regular files: always. Pipes: never. Character devices: sometimes (if the driver implements lseek in its file_operations).",
  "llm_judge_instructions": "Award full credit for the standard rules and caveat about character devices potentially supporting lseek."
}
```

---

## Question 22 [2 point(s)]

At each level of the page table, we look up an entry which contains (the upper bits of) a pointer to another page, until the last one points to the desired data page. Do you think these pointers contain virtual or physical addresses? Why?

```json
{
  "problem_id": "22",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "These pointers contain physical addresses, because using virtual addresses inside the page table would require further address translation and could lead to recursion; the CPU uses physical frame addresses in the page table.",
  "llm_judge_instructions": "Award full credit for stating that page-table entries hold physical addresses and explaining the rationale."
}
```

---

## Question 23 [2 point(s)]

Is the size of a page consistent on all platforms that Linux runs on, or does it vary between platforms? How do you know?

```json
{
  "problem_id": "23",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "The page size varies between architectures; PAGE_SIZE is architecture-dependent, defined via PAGE_SHIFT/PAGESIZE per architecture.",
  "llm_judge_instructions": "Award full credit for noting architecture dependence of page size."
}
```

---

## Question 24 [3 point(s)]

Fill in the missing parts in the table below relating to file permissions in octal and symbolic form.
OctalSymbolic
0666(a) rw-rw-rw-
(b) 0674
rw-rwxr–
0775(c) rwxrwxr-x
(d) 0544r-xr–r–
0511
(e) r-x--x--x
(f) 0222-w–w–w-

```json
{
  "problem_id": "24",
  "points": 3,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "(a) 0666 -> rw-rw-rw-; (b) 0674 -> rw-rwxr--; (c) 0775 -> rwxrwxr-x; (d) 0544 -> r-xr--r--; (e) 0511 -> r-x--x--x; (f) 0222 -> -w--w--w-",
  "llm_judge_instructions": "Award full credit for the correct octal-to-symbolic mappings listed above."
}
```

---

## Question 25 [2 point(s)]

Consider the following code:
#include <stdio.h>
int main(int argc, char *argv[])
{
  printf("Hello!  The number is %d!\n", NUMBER);
}
(a) How can you compile this so, when run, it outputs “Hello!  The number is 42!” (rather than reporting a compilation error)?
(b) What is one situation in which the technique you used in a) is useful (beyond those shown in class tutorials)?

```json
{
  "problem_id": "25",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "a) Compile with -DNUMBER=42. b) Useful for changing constants at compile time or for conditional compilation (e.g., #ifdef).",
  "llm_judge_instructions": "Award full credit for describing the -DNUMBER=42 compile-time definition and a valid use-case for compile-time constants."
}
```

---

## Question 26 [2 point(s)]

Python scripts importing from the bcc library can monitor all system calls on a system and arbitrary function calls in any process and in the kernel. Can regular python scripts or other userspace programs do this? Why or why not? Explain.

```json
{
  "problem_id": "26",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "Regular Python scripts cannot monitor arbitrary kernel and user-space events. Such monitoring requires BPF; ptrace can monitor a single process, but broad kernel-space monitoring requires BPF (or specialized tooling).",
  "llm_judge_instructions": "Award full credit for recognizing the need for BPF or kernel-space facilities and the limitations of regular userspace tools."
}
```

---

## Question 27 [2 point(s)]

Give an example of how an eBPF program can access a field in a task struct. What task struct is being accessed?

```json
{
  "problem_id": "27",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "An example is accessing the current task's task_struct using current in eBPF programs, such as bpfgetcurrentpidtgid() to obtain the user-visible PID of the current task.",
  "llm_judge_instructions": "Award full credit for describing accessing current task’s task_struct (task data) via BPF helpers like bpfgetcurrentpidtgid()."
}
```

---

## Question 28 [3 point(s)]

How often is thefilter()function called in (the original version of) bpfprogram.c when tracing system calls?  It it called for every system call made on the system, every system call made by the specified process, or every time a process running 3000shell makes a system call?  How can you tell this from the code? What experiment(s) did you do to verify your interpretation of the code?

```json
{
  "problem_id": "28",
  "points": 3,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "It runs for every system call made on the system. This is visible via a tracepoint probe of every system call exit in the code; removing the filter() call yields system calls from every process. Experiments include removing lines that call filter() and observing system call output.",
  "llm_judge_instructions": "Award full credit for describing the global system-call tracing behavior and how code changes reveal it."
}
```

---

## Question 29 [2 point(s)]

What is a way to load code into the kernel without it being verified for safety?  What limits are placed on such code, relative to other kernel code?

```json
{
  "problem_id": "29",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems"],
  "answer": "You can load code as a kernel module (insmod). Kernel modules can do essentially anything and are not subject to the same safety verification as core kernel code.",
  "llm_judge_instructions": "Award full credit for describing kernel modules as an unsafe-loading mechanism and noting the relative lack of verification compared to core kernel code."
}
```