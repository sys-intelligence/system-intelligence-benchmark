# COMP 3000B: Operating Systems Winter 2020 Final

```json
{
  "exam_id": "comp3000_winter_2020_final",
  "test_paper_name": "COMP 3000B: Operating Systems Winter 2020 Final",
  "course": "COMP3000",
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
  "tags": ["bash","unix","shell"],
  "answer": "The terminal driver provides input to the shell via a character device like /dev/pts/N; this is not a regular file. Bash reads user input from that device.",
  "llm_judge_instructions": "1 pt: Award if the response identifies that bash reads from the terminal/tty (e.g., /dev/pts/N). 1 pt: Award if the response states that this is a character device and not a regular file."
}
```

---

## Question 2 [1 point]

When you type the command ls > ls.log at a bash shell prompt, what process opens the file ls.log for writing, bash, ls, or another?

```json
{
  "problem_id": "2",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["bash","redirection","unix"],
  "choices": ["bash","ls","another"],
  "answer": "bash",
  "llm_judge_instructions": "1 pt: Award if the answer is exactly \"bash\"."
}
```

---

## Question 3 [2 point(s)]

When you type ls -la at a bash prompt, what system call does bash use to receive user input? What system call does bash use to pass the -la argument to ls?

```json
{
  "problem_id": "3",
  "points": 2,
  "type": "Freeform",
  "tags": ["bash","syscall","shell"],
  "answer": "read, execve",
  "llm_judge_instructions": "1 pt: Award if the response identifies 'read' (or equivalent) as the syscall used to receive user input. 1 pt: Award if the response identifies 'execve' (or equivalent) as the syscall used to execute ls with arguments."
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
  "tags": ["c-library","system-calls","fgets","ioctl","snprintf"],
  "answer": "a) read, b) ioctl, c) none",
  "llm_judge_instructions": "1 pt for part (a): award if the answer indicates fgets commonly results in read. 1 pt for part (b): award if the answer indicates ioctl. 1 pt for part (c): award if the answer indicates snprintf does not perform a syscall."
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
  "tags": ["process-management","exit-status","wait","ipc"],
  "answer": "B calls exit with a return code indicating failure. A calls wait to get B’s exit code.",
  "llm_judge_instructions": "1 pt: Award for stating that B exits with a non-zero exit status to indicate failure. 1 pt: Award for stating that A uses wait or waitpid to retrieve B's exit status (and can inspect it)."
}
```

---

## Question 6 [2 point(s)]

If you decided you didn’t want to run any pre-installed binaries and instead just wanted to run your own versions when you type in commands at a shell prompt, how could you do this?  Would this change prevent other users of the system from using system binaries? Explain briefly.

```json
{
  "problem_id": "6",
  "points": 2,
  "type": "Freeform",
  "tags": ["path","shell","environment"],
  "answer": "You would change your PATH environment variable (via shell config files like .bashrc/.bash_profile) to only include directories you control, excluding /bin, /usr/bin, etc. This would not affect other users; they still have their own PATHs and can use system binaries.",
  "llm_judge_instructions": "1 pt: Award for describing changing or reordering PATH to prioritize user directories. 1 pt: Award for explicitly stating this change is per-user and does not prevent other users from using system binaries."
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
  "tags": ["signals","sleep","SA_RESTART"],
  "answer": "The signal handler will run immediately, and then the sleep system call will return (potentially resuming if SA_RESTART is not set).",
  "llm_judge_instructions": "1 pt: Award for stating that the signal handler runs immediately (signal is delivered while sleeping). 1 pt: Award for explaining that sleep returns after the handler and mentioning the role of SA_RESTART or interrupted syscalls as a caveat."
}
```

---

## Question 8 [2 point(s)]

SIGPIPE is sent to a process to indicate a broken pipe, i.e., a write to a pipe that has no readers (but did previously).  Alice, upon learning about SIGPIPE, says this is stupid, because the write would just return an error.  Bob replies that SIGPIPE is useful just like SIGCHLD is.  Is Alice right or is Bob? Explain how the signals are similar and a situation when SIGPIPE would be useful.

```json
{
  "problem_id": "8",
  "points": 2,
  "type": "Freeform",
  "tags": ["signals","SIGPIPE","SIGCHLD","ipc"],
  "answer": "The key benefit of SIGPIPE is informing a process that a pipe is broken even if it isn’t in the middle of doing a write. In a producer/consumer scenario, the producer can react immediately if the consumer has terminated, rather than waiting for a write to error or a later system call.",
  "llm_judge_instructions": "1 pt: Award for explaining that SIGPIPE notifies a process of a broken pipe (immediate notification). 1 pt: Award for giving a concrete example or comparing to SIGCHLD (e.g., producer/consumer scenario or immediate termination notification)."
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
  "tags": ["permissions","uid","euid","gid","egid"],
  "answer": "The process can read files owned by uid 1000 with owner-read bit set, files in group 1021 with group-read bit set, and any file with 'other' read bit set. Directories along the path must be accessible (read+execute) for the user, group, or others.",
  "llm_judge_instructions": "1 pt: Award for describing owner/group/other permission checks (owner read if uid matches, group read if GID matches, otherwise other). 1 pt: Award for noting that directory execute/search permissions on path components are also required."
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
  "tags": ["ssh","keys","authentication"],
  "answer": "The id_rsa file contains the user’s private key, and id_rsa.pub contains the public key. The public key is installed on remote systems (authorized_keys), and the private key is kept secret to authenticate the user.",
  "llm_judge_instructions": "1 pt: Award for identifying id_rsa as the private key and id_rsa.pub as the public key. 1 pt: Award for explaining that the public key is placed in authorized_keys on the server and the private key remains secret on the client for authentication."
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
  "tags": ["inodes","hard-links","filesystem"],
  "answer": "Yes. Two filenames can be hard links to the same inode, meaning they are different names for the same underlying file contents.",
  "llm_judge_instructions": "1 pt: Award for stating that hard links allow multiple directory entries to refer to the same inode. 1 pt: Award for clarifying that they are the same file contents and metadata (same inode) under different names."
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
  "tags": ["ext4","superblock","recovery"],
  "answer": "No. The superblocks are essential to mounting the filesystem; recovery would require reconstructing parameters or forensic recovery, which is non-trivial.",
  "llm_judge_instructions": "1 pt: Award for stating that recovery is not easy or straightforward (i.e., not easily recoverable). 1 pt: Award for explaining that superblocks contain critical filesystem metadata and that reconstructing them without backups is difficult."
}
```

---

## Question 13 [1 point]

If you want the standard output of one program to be fed to the standard input of another program directly (without storing any data on disk), how could you do this without using the | operator? Explain with a short example.

```json
{
  "problem_id": "13",
  "points": 1,
  "type": "Freeform",
  "tags": ["pipes","ipc","named-pipe","fifo"],
  "answer": "Create a named pipe (FIFO) with mkfifo, then redirect: ls > mypipe; wc < mypipe.",
  "llm_judge_instructions": "1 pt: Award if the response mentions creating a named pipe (mkfifo) and gives a correct example of using it to connect writer and reader (e.g., ls > mypipe and wc < mypipe)."
}
```

---

## Question 14 [2 point(s)]

Below is an implementaiton of sem_wait(). Does this version cause the process to sleep while waiting for the lock to be freed? Do you expect this implementation to work reliably in practice? Explain briefly.

```c
void sem_wait(int *lock)
{
  while (*lock == 0) {
    /*
    wait
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
  "tags": ["synchronization","sem","busy-wait","race-conditions"],
  "answer": "This version busy-waits; it does not sleep. It will not work reliably due to a race between checking *lock and setting it to 0; atomicity is not guaranteed.",
  "llm_judge_instructions": "1 pt: Award for identifying that the implementation busy-waits (does not sleep). 1 pt: Award for explaining the race condition (check-then-set is not atomic) and noting the need for atomic test-and-set or proper blocking primitives."
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
  "tags": ["processes","threads","kernel"],
  "answer": "From an API perspective, creating a process is simpler (fork) than a thread (pthread_create). The kernel does more work to create a process (address space duplication) while threads share the address space and require coordination.",
  "llm_judge_instructions": "1 pt: Award for stating which is simpler from the API perspective (e.g., fork simpler). 1 pt: Award for explaining which requires more kernel work (process creation/address-space duplication) and why."
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
  "tags": ["linux-kernel","char-device","llseek","file_operations"],
  "answer": "Add an llseek function (e.g., mymodule_llseek) with the same signature as lseek, register it in the device’s file_operations structure as the llseek entry so the kernel calls it when a user calls lseek on the device.",
  "llm_judge_instructions": "1 pt: Award for naming/identifying an llseek handler for the character device. 1 pt: Award for explaining that it must be registered in the device's file_operations->llseek so the kernel will call it on lseek calls."
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
  "tags": ["uids","permissions","kernel"],
  "answer": "uid determines process ownership for signals and certain ownership checks; euid determines the resources the process can access (e.g., file permissions).",
  "llm_judge_instructions": "1 pt: Award for stating that uid represents the real user identity (ownership). 1 pt: Award for stating that euid is used for access control/permission checks (e.g., file access)."
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
  "tags": ["groups","kernel","newgrp","setuid"],
  "answer": "No. The kernel tracks GIDs (group IDs) on processes and files, not human group names. Tools like newgrp can change the active group via setuid utilities.",
  "llm_judge_instructions": "1 pt: Award for stating that the kernel tracks numeric GIDs, not human-readable group names. 1 pt: Award for noting that user-level tools map names to GIDs (e.g., via /etc/group) and that newgrp/setuid mechanisms change active GIDs."
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
  "tags": ["mmap","virtual-memory","physical-memory"],
  "answer": "A process can largely control virtual memory placement via the address space it maps into. Physical memory placement is largely determined by the kernel and is not directly controllable by the process.",
  "llm_judge_instructions": "1 pt: Award for stating that a process can control virtual address placement (e.g., via mmap address hint/flags). 1 pt: Award for stating that physical placement is controlled by the kernel and not under direct process control."
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
  "tags": ["virtual-memory","address-space","shared-memory"],
  "answer": "Two processes can have data at the same virtual address, but they refer to different memory spaces. They can share data at the same physical address via shared memory or mmap of the same file, but virtual addresses may differ.",
  "llm_judge_instructions": "1 pt: Award for explaining that different processes can have data at the same virtual address because address spaces are distinct. 1 pt: Award for explaining that the same physical page can be shared (shared memory or shared mappings) so both processes see the same physical memory."
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
  "tags": ["lseek","regular-files","pipes","character-devices"],
  "answer": "Regular files: always. Pipes: never. Character devices: sometimes (depends on device support in file_operations).",
  "llm_judge_instructions": "1 pt: Award for stating 'regular files: always' and brief justification. 1 pt: Award for stating 'pipes: never' and brief justification. 1 pt: Award for stating 'character devices: sometimes' and noting it depends on whether the device implements llseek in file_operations."
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
  "tags": ["page-table","physical-address","virtual-address"],
  "answer": "These pointers contain physical addresses, since the page table maps virtual to physical addresses and must resolve to actual RAM addresses.",
  "llm_judge_instructions": "1 pt: Award for stating that page table entries hold physical addresses (frame numbers). 1 pt: Award for a correct justification that page tables must reference physical frames to map virtual pages to RAM."
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
  "tags": ["page-size","architectures","PAGE_SIZE"],
  "answer": "The page size is not consistent across platforms; it varies by architecture (PAGE_SIZE/PAGE_SHIFT definitions differ).",
  "llm_judge_instructions": "1 pt: Award for stating that page size varies by platform/architecture. 1 pt: Award for referencing PAGE_SIZE/PAGE_SHIFT or architecture-specific definitions as evidence."
}
```

---

## Question 24 [3 point(s)]

Fill in the missing parts in the table below relating to file permissions in octal and symbolic form.
Octal Symbolic
0666(a) rw-rw-rw-
(b) 0674
rw-rwxr–
0775(c) rwxrwxr-x
(d) 0544r-xr–r–
0511(e) r-x--x--x
(f) 0222-w–w–w-

```json
{
  "problem_id": "24",
  "points": 3,
  "type": "Freeform",
  "tags": ["file-permissions","octal","symbolic"],
  "answer": "a) rw-rw-rw-, b) rw-rwxr--, c) rwxrwxr-x, d) r-xr--r--, e) r-x--x--x, f) -w--w--w-",
  "llm_judge_instructions": "Award 0.5 pts for each correctly completed symbolic form (six items total, 6 * 0.5 = 3.0 pts). Partial credit: 0.5 pts per exact match for items a through f."
}
```

---

## Question 25 [2 point(s)]

Consider the following code:
```c
#include <stdio.h>
int main(int argc, char *argv[])
{
  printf("Hello!  The number is %d!\n", NUMBER);
}
```
(a)  How can you compile this so, when run, it outputs “Hello!  The number is 42!”  (rather than
reporting a compilation error)?
(b)  What is one situation in which the technique you used in a) is useful (beyond those shown in
class tutorials)?

```json
{
  "problem_id": "25",
  "points": 2,
  "type": "Freeform",
  "tags": ["compile-define","conditional-compilation","preprocessor"],
  "answer": "a) Add -DNUMBER=42 to the compilation command. b) Useful for changing constants at compile time or enabling conditional compilation (#ifdef).",
  "llm_judge_instructions": "1 pt: Award for specifying use of -DNUMBER=42 (or equivalent preprocessor definition). 1 pt: Award for giving a plausible additional use case (e.g., compile-time configuration, platform-specific constants, toggling features via #ifdef)."
}
```

---

## Question 26 [2 point(s)]

Python scripts importing from the bcc library can monitor all system calls on a system and arbitrary function calls in any process and in the kernel.  Can regular python scripts or other userspace programs do this? Why or why not? Explain.

```json
{
  "problem_id": "26",
  "points": 2,
  "type": "Freeform",
  "tags": ["ebpf","bcc","system-monitoring","kernel"],
  "answer": "Regular Python scripts cannot monitor all system calls and kernel events; you need BPF-based tooling (e.g., bcc) and often root privileges. ptrace is limited to a single process; BPF allows broader monitoring with proper privileges.",
  "llm_judge_instructions": "1 pt: Award for stating that non-BPF userspace scripts cannot monitor system-wide kernel events and that BPF/bcc is required. 1 pt: Award for mentioning required privileges (root) and/or contrast with ptrace's per-process limitation."
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
  "tags": ["ebpf","task_struct","current"],
  "answer": "An example is using bpf.get_current_pid_tgid() to access the current task’s pid; the task_struct accessed is the current task's task_struct via the 'current' pointer.",
  "llm_judge_instructions": "1 pt: Award for giving a concrete example or helper (e.g., bpf_get_current_task or bpf_get_current_pid_tgid) used to access a field. 1 pt: Award for stating that the accessed struct is the current task's task_struct (and citing a field like pid or tgid)."
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
  "tags": ["bpf","tracing","system-calls","filter"],
  "answer": "It runs for every system call made on the system. This can be inferred from the tracepoint probe of every system call exit (line 69) and the behavior when filter() is removed (more output from all processes).",
  "llm_judge_instructions": "1 pt: Award for stating that filter() is invoked for every system call on the system. 1 pt: Award for explaining how the code (tracepoint probe registration or attach point) shows this. 1 pt: Award for describing an experiment or observation used to verify this (e.g., removing the filter increases output from all processes or running a test process and observing events)."
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
  "tags": ["kernel-modules","insmod","safety"],
  "answer": "Loadable kernel modules via insmod; such code has no special safety restrictions beyond normal kernel code and can perform a broad range of actions (within the kernel’s privileges).",
  "llm_judge_instructions": "1 pt: Award for mentioning loadable kernel modules (e.g., insmod) as a way to load unchecked code. 1 pt: Award for stating that such modules are not subject to BPF-like safety verification and have broad kernel privileges (subject to kernel/module signing/configuration policies)."
}
```

---