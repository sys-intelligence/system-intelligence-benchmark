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
  "tags": ["operating-systems","bash","shell"],
  "answer": "bash reads from a numbered file /dev/pts (such as /dev/pts/0) in order to obtain user input. This file is a character device, it is not a regular file.",
  "llm_judge_instructions": "Award 2 points for identifying /dev/pts (a terminal device file) as the source of user input and noting that it is a character device and not a regular file. Award 0 points otherwise."
}
```

---

## Question 2 [1 point(s)]

When you type the command ls > ls.log at a bash shell prompt, what process opens the file ls.log for writing, bash, ls, or another?

```json
{
  "problem_id": "2",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["bash","filesystem","process-management"],
  "choices": ["bash","ls","another"],
  "answer": "bash"
}
```

---

## Question 3 [2 point(s)]

When you typels -la at a bashprompt,  what system call does bash use to receive user input? What system call does bash use to pass the-laargument to ls?

```json
{
  "problem_id": "3",
  "points": 2,
  "type": "Freeform",
  "tags": ["system-calls","bash","process-management"],
  "answer": "read, execve",
  "llm_judge_instructions": "Award 2 points total: 1 point for correctly identifying read (to receive user input) and 1 point for execve (to pass the -la argument to ls). Partial credit if only one is correct."
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
  "tags": ["library-functions","system-calls"],
  "answer": "a) read, b) ioctl, c) none",
  "llm_judge_instructions": "Award 1 point for each correct item: (a) fgets -> read, (b) ioctl -> ioctl, (c) snprintf -> none. Provide 0 points for incorrect items."
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
  "tags": ["process-management","ipc","exit-status"],
  "answer": "B calls exit with a return code indicating failure. A calls wait to get B’s exit code.",
  "llm_judge_instructions": "Award 2 points for stating that the child exits with a status and the parent collects it with wait; 0 points otherwise."
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
  "tags": ["environment","PATH","shell-configuration"],
  "answer": "You would change your PATH environment variable (by changing your shell configuration files, e.g., .bashrc, .bashprofile, .profile) to only list your directories, excluding /bin, /usr/bin, etc. This change wouldn’t affect any other users on the system.",
  "llm_judge_instructions": "Award 2 points for describing modifying PATH to prioritize user directories and remove system bin paths; 0 points otherwise."
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
  "tags": ["signals","scheduling"],
  "answer": "The signal handler will run immediately, and then once the signal finishes the sleep system call will return without having finished the sleep. If the SA_RESTART flag is not set, the sleep may terminate early.",
  "llm_judge_instructions": "Award 2 points for stating that the handler runs immediately and the sleep may be interrupted; partial credit 1 point for mentioning immediate handling but not the interrupting effect."
}
```

---

## Question 8 [2 point(s)]

SIGPIPE is sent to process to indicate a broken pipe, i.e., a write to a pipe that has no readers (but did previously).  Alice, upon learning about SIGPIPE, says this is stupid, because the write would just return an error.  Bob replies that SIGPIPE is useful just like SIGCHLD is.  Is Alice right or is Bob? Explain how the signals are similar and a situation when SIGPIPE would be useful.

```json
{
  "problem_id": "8",
  "points": 2,
  "type": "Freeform",
  "tags": ["signals","sigpipe","sigchild"],
  "answer": "The key benefit of SIGPIPE is informing a process that a pipe is broken even if it isn’t in the middle of doing a write. In a producer/consumer situation using a pipe, the producer could be spending a considerable amount of time producing, assuming that the consumer is waiting; with SIGPIPE it will be immediately informed that something has gone wrong with the consumer and can take corrective action (or just terminate). This is similar to SIGCHLD, in that SIGCHLD tells the parent immediately that its child has terminated, while a call to wait would result in a significant delay in getting this information to the parent.",
  "llm_judge_instructions": "Award 2 points for recognizing SIGPIPE's immediate notification benefit and its similarity to SIGCHLD; 0 points otherwise."
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
  "tags": ["permissions","uid","gid"],
  "answer": "The process can read files owned by uid 1000 with owner read bit set, files in group 1021 with group read bit set, and files with other read bit set. Access also requires traversable directories with execute permissions and readable paths.",
  "llm_judge_instructions": "Award 2 points for mentioning owner, group, and other read permissions and the need to traverse directories with appropriate execute permissions. Partial credit 1 point for mentioning a subset correctly."
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
  "answer": "The id_rsa file contains a user’s private key, and id_rsa.pub contains the public key. They are used to authenticate to a remote system by copying the contents of id_rsa.pub to the remote system’s authorized_keys file.",
  "llm_judge_instructions": "Award 2 points for correctly describing private vs public keys and their use in SSH authentication; 0 points otherwise."
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
  "tags": ["inode","hard-links"],
  "answer": "Two filenames can both be hard links to the same inode. They are just names for the same file, sharing the same inode.",
  "llm_judge_instructions": "Award 2 points for explaining hard links share the same inode; 0 otherwise."
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
  "tags": ["filesystem","superblock","ext4"],
  "answer": "You cannot easily recover from erasing the primary and backup superblocks of a filesystem, as these are essential to mounting a filesystem. Recovery would involve reconstructing the superblock or forensic data recovery, which is non-trivial.",
  "llm_judge_instructions": "Award 2 points for noting the essential role of superblocks and the difficulty of recovery; 0 otherwise."
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
  "tags": ["pipes","ipc","named-pipe"],
  "answer": "You would create a named pipe, and have one program use the pipe for standard out and the other for standard in. For example: mkfifo mypipe; (ls > mypipe &); wc < mypipe",
  "llm_judge_instructions": "Award 1 point for describing a named pipe (FIFO) solution and a minimal example; 0 otherwise."
}
```

---

## Question 14 [2 point(s)]

Below is an implementaiton ofsem_wait(). Does this version cause the process to sleep while waiting for the lock to be freed? Do you expect this implementation to work reliably in practice? Explain briefly.

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
  "tags": ["concurrency","semaphore","locking"],
  "answer": "This version does not cause the process to sleep if the lock is currently taken; instead, it busy waits. It will not work reliably in practice because the check and assignment are not atomic, allowing a race to modify *lock between checks.",
  "llm_judge_instructions": "Award 2 points for identifying busy-waiting and lack of atomicity; 0 points otherwise."
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
  "answer": "A process is simpler to create from an API perspective than a thread, as a process can be created using fork, while threads are created using pthread_create. Process creation involves more kernel work to copy address space; threads share address space.",
  "llm_judge_instructions": "Award 2 points for the comparison and rationale about kernel work; 0 otherwise."
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
  "tags": ["linux-kernel","device-driver","lseek"],
  "answer": "Add an llseek function (e.g., mymodule_llseek) with the same arguments as lseek, and register it in the file_operations struct for the device so that it is called when lseek is invoked.",
  "llm_judge_instructions": "Award 2 points for mentioning llseek handler and registering it in the file_operations; 0 otherwise."
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
  "tags": ["permissions","security","uid"],
  "answer": "The kernel uses the uid to determine process ownership (control of signals, etc.), while the euid is used to determine which resources (files, etc.) the process can access.",
  "llm_judge_instructions": "Award 2 points for distinguishing ownership versus access checks; 0 otherwise."
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
  "tags": ["groups","kernel"],
  "answer": "The kernel doesn’t know the group names directly; it only knows the GIDs. Changing the active group is handled by user-space utilities (e.g., newgrp) which can escalate privileges to change gid.",
  "llm_judge_instructions": "Award 2 points for noting the kernel knows GIDs rather than group names and mentioning user-space tools for changing groups; 0 otherwise."
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
  "answer": "A process can mostly control where a file is mmap’d into virtual memory, but has almost no control over where it is mapped into physical memory; the kernel decides physical placement.",
  "llm_judge_instructions": "Award 2 points for distinguishing virtual address control and limited control over physical memory; 0 otherwise."
}
```

---

## Question 20 [2 point(s)]

Can two processes have data at the same virtual address? What about at the same physical address? Explain.

```json
{
  "problem_id": "20",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory","shared-memory"],
  "answer": "Two processes can have data at the same virtual address, but they refer to different memory spaces. They can share data at the same physical address if they mmap the same file or use a shared memory segment.",
  "llm_judge_instructions": "Award 2 points for explaining virtual address isolation and shared physical pages; partial credit 1 point for mentioning either virtual isolation or shared physical memory correctly."
}
```

---

## Question 21 [3 point(s)]

For each of the following, state and explain whether they support lseek operations always, some­times, or never: regular files, pipes, character devices

```json
{
  "problem_id": "21",
  "points": 3,
  "type": "Freeform",
  "tags": ["lseek","files","pipes","devices"],
  "answer": "Regular files always support lseek operations. Pipes never support lseek. Character devices sometimes support lseek if they implement lseek in their file_operations.",
  "llm_judge_instructions": "Award 2 points for correct classification of regular files and pipes; award 1 point for correctly stating character devices sometimes support lseek and mentioning that this depends on their implementing an llseek handler. Total 3 points. 0 points otherwise."
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
  "tags": ["page-table","addressing"],
  "answer": "These pointers contain physical addresses, because looking up virtual addresses would require further virtual-to-physical translations at each level.",
  "llm_judge_instructions": "Award 2 points for stating the pointers are physical addresses and providing a rationale; 0 otherwise."
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
  "tags": ["page-size","architecture"],
  "answer": "The page size is not consistent because PAGE_SIZE varies between different architectures. This is reflected in architecture-specific definitions like PAGE_SHIFT and PAGESIZE.",
  "llm_judge_instructions": "Award 2 points for noting architecture-dependent page size and referencing architecture-specific constants; 0 otherwise."
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
  "tags": ["permissions","octal","symbolic"],
  "answer": "(a) rw-rw-rw-; (b) rw-rwxr--; (c) rwxrwxr-x; (d) r-xr--r--; (e) r-x--x--x; (f) ----w--w-",
  "llm_judge_instructions": "Award 0.5 points for each correct entry (a) through (f). There are six items; each correct item receives 0.5 points for a total of 3 points. Award 0 points for incorrect items."
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
(a)  How can you compile this so, when run, it outputs “Hello!  The number is 42!”  (rather than reporting a compilation error)?
(b)  What is one situation in which the technique you used in a) is useful (beyond those shown in class tutorials)?

```json
{
  "problem_id": "25",
  "points": 2,
  "type": "Freeform",
  "tags": ["compile-time-constants","macros","preprocessor"],
  "answer": "a) Use -DNUMBER=42 on the compiler command line. b) Useful for changing constants or system parameters at compile time, e.g., to enable conditional compilation.",
  "llm_judge_instructions": "Award 2 points total: 1 point for each part; partial credit if only one part is correct."
}
```

---

## Question 26 [2 point(s)]

Python scripts importing from the bcc library can monitor all system calls on a system and arbi­trary function calls in any process and in the kernel.  Can regular python scripts or other userspace programs do this? Why or why not? Explain.

```json
{
  "problem_id": "26",
  "points": 2,
  "type": "Freeform",
  "tags": ["ebpf","kernel","monitoring"],
  "answer": "Regular python scripts, or any non-BPF userspace program, cannot monitor arbitrarily. Processes are isolated; to monitor across processes you need BPF; root alone is not sufficient without BPF.",
  "llm_judge_instructions": "Award 2 points for explaining limitation and need for BPF; 0 points otherwise."
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
  "tags": ["ebpf","taskstruct","current"],
  "answer": "There are many examples in BPF code; one is accessing current->pid or current->tgid via bpf_get_current_pid_tgid() which reads from the task_struct of the current task.",
  "llm_judge_instructions": "Award 2 points for identifying access to fields like current->pid/tgid and naming current task's task_struct; 0 otherwise."
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
  "tags": ["ebpf","tracing","syscalls"],
  "answer": "It runs for every system call made on the system. This is visible in bpfprogram.c with a tracepoint probe of every system call exit. If you remove the filter() call, you see system calls from every process.",
  "llm_judge_instructions": "Award 3 points for correctly describing the global system-wide tracing and providing the code-based justification plus the experimental verification concept. 0 otherwise."
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
  "tags": ["kernel-module","insmod","safety"],
  "answer": "You can load code using a kernel module (i.e., insmod). No special safety checks limit such code relative to built-in kernel code; modules can do anything",
  "llm_judge_instructions": "Award 2 points for recognizing kernel modules as a means to load unsigned code and noting it has similar privileges to built-in code; 0 points otherwise."
}
```

---