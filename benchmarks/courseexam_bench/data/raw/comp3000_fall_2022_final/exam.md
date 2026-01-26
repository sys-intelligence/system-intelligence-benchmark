# COMP 3000 Fall 2022 Final

```json
{
  "exam_id": "comp3000_fall_2022_final",
  "test_paper_name": "COMP 3000 Fall 2022 Final",
  "course": "COMP 3000",
  "institution": "Carleton University",
  "year": 2022,
  "score_total": 72,
  "num_questions": 47
}
```

---

## Question 1 [2 point(s)]

In what circumstances would you expect the signal handler in 3000shell2.c to be called? Would you expect this to happen often?

```json
{
  "problem_id": "1",
  "points": 2,
  "type": "Freeform",
  "tags": ["signals", "operating-systems"],
  "answer": "SIGHUP or SIGCHLD signals",
  "llm_judge_instructions": "Award 2 points total: 1 point for identifying SIGHUP and/or SIGCHLD signals; 1 point for a reasonable explanation of when each signal would be received (SIGHUP rarely, SIGCHLD on child termination). If only one signal is named, credit partial accordingly."
}
```

---

## Question 2 [2 point(s)]

If you strace processes on the class VM, do you generally expect to see fork system calls? Why or why not?

```json
{
  "problem_id": "2",
  "points": 2,
  "type": "Freeform",
  "tags": ["syscalls", "process-management", "virtualization"],
  "answer": "Clone is used for fork; you don’t see fork syscalls because the C library implements fork by calling clone.",
  "llm_judge_instructions": "Award 2 points total: 1 point for recognizing that fork is implemented via clone; 1 point for explaining that the C library handles this, so direct fork syscalls may not appear."
}
```

---

## Question 3 [2 point(s)]

What determines the available internal commands for a shell? What about the available external commands?

```json
{
  "problem_id": "3",
  "points": 2,
  "type": "Freeform",
  "tags": ["shell", "commands"],
  "answer": "Internal commands are implemented by the shell itself; external commands come from programs in PATH directories.",
  "llm_judge_instructions": "Award 2 points: 1 for internal commands provided by the shell, 1 for external commands provided by executables found in PATH."
}
```

---

## Question 4a [1 point]

For each of the following questions, answer unshare, chroot, both, or neither. (0.5 for correct unshare classification, 0.5 for correct chroot classification.)

(a) Can change how file paths are interpreted

```json
{
  "problem_id": "4a",
  "points": 1,
  "type": "Freeform",
  "tags": ["namespacing", "unshare", "chroot"],
  "answer": "both",
  "llm_judge_instructions": "Award 0.5 points for correctly identifying unshare, and 0.5 points for correctly identifying chroot. Partial credit if only one is correct."
}
```

---

## Question 4b [1 point]

(b) Can change the PID’s associated with processes

```json
{
  "problem_id": "4b",
  "points": 1,
  "type": "Freeform",
  "tags": ["namespacing", "unshare"],
  "answer": "unshare",
  "llm_judge_instructions": "Award 1 point for correctly identifying unshare. No partial credit beyond that."
}
```

---

## Question 4c [1 point]

(c) Creates persistent files

```json
{
  "problem_id": "4c",
  "points": 1,
  "type": "Freeform",
  "tags": ["namespacing", "unshare", "chroot"],
  "answer": "neither",
  "llm_judge_instructions": "Award 1 point for correctly identifying neither. No partial credit."
}
```

---

## Question 4d [1 point]

(d) Can change how UID’s are interpreted

```json
{
  "problem_id": "4d",
  "points": 1,
  "type": "Freeform",
  "tags": ["namespacing", "unshare"],
  "answer": "unshare",
  "llm_judge_instructions": "Award 1 point for correctly identifying unshare."
}
```

---

## Question 4e [1 point]

(e) execve’s a new executable

```json
{
  "problem_id": "4e",
  "points": 1,
  "type": "Freeform",
  "tags": ["execve", "namespacing"],
  "answer": "both",
  "llm_judge_instructions": "Award 1 point for correctly identifying both."
}
```

---

## Question 5 [1 point]

When doing a call to fork(), how does the parent get the PID of the child process?

```json
{
  "problem_id": "5",
  "points": 1,
  "type": "Freeform",
  "tags": ["process-management"],
  "answer": "The return value of fork, if it is greater than zero, is the PID of the child process.",
  "llm_judge_instructions": "Award 1 point for stating that fork returns the child’s PID in the parent (positive return value)."
}
```

---

## Question 6 [2 point(s)]

Is there a potential risk in running sudo busybox --install on the class VM? Why or why not? Assume you are running it in the normal student account just after login.

```json
{
  "problem_id": "6",
  "points": 2,
  "type": "Freeform",
  "tags": ["security", "busybox"],
  "answer": "Yes; it creates hard links to busybox in standard directories using common program names, potentially replacing standard tools. BusyBox checks for existence of those files, but it could still cause changes in system behavior.",
  "llm_judge_instructions": "Award 2 points: 1 for explaining what the command does (creates links), 1 for discussing potential risk (replacement of standard tools) or safety due to busybox checks; partial credit if only one aspect is described."
}
```

---

## Question 7a [1 point]

(a) Could any of the above commands cause loss of data? Assume that nothing exists in the current directory with the name “myimage” and “mp”. (Yes or No)

```json
{
  "problem_id": "7a",
  "points": 1,
  "type": "Freeform",
  "tags": ["filesystem", "data-safety"],
  "answer": "No",
  "llm_judge_instructions": "Award 1 point for answering No and brief justification if provided."
}
```

---

## Question 7b [1 point]

(b) How many writes system calls were needed to create file1?

```json
{
  "problem_id": "7b",
  "points": 1,
  "type": "Freeform",
  "tags": ["system-calls", "filesystem"],
  "answer": "2",
  "llm_judge_instructions": "Award 1 point for identifying 2 writes were used to create file1."
}
```

---

## Question 7c [2 points]

(c) Which of the above commands require root privileges? Why?

```json
{
  "problem_id": "7c",
  "points": 2,
  "type": "Freeform",
  "tags": ["permissions", "root"],
  "answer": "mount requires root privileges because it changes the filesystem and directory structure.",
  "llm_judge_instructions": "Award 2 points: 1 point for identifying that mount requires root, 1 point for explaining why (filesystem changes, directory structure)."
}
```

---

## Question 7d [2 points]

(d) What filesystem is file1 stored in? What about file2? Why?

```json
{
  "problem_id": "7d",
  "points": 2,
  "type": "Freeform",
  "tags": ["filesystem"],
  "answer": "file1 is stored in the root filesystem on /dev/sda2; file2 is stored in the mounted myimage filesystem (mounted at mp).",
  "llm_judge_instructions": "Award 2 points: 1 for file1 location (root filesystem /dev/sda2), 1 for file2 being in the mounted filesystem (myimage) mounted at mp."
}
```

---

## Question 7e [2 points]

(e) Did the creation of file1 increase the amount of data stored in /dev/sda2? What about file2? Explain briefly.

```json
{
  "problem_id": "7e",
  "points": 2,
  "type": "Freeform",
  "tags": ["filesystem"],
  "answer": "Yes for file1 (root filesystem on /dev/sda2) and Yes for file2 (space used in myimage’s filesystem; its image is stored in the root filesystem).",
  "llm_judge_instructions": "Award 2 points: 1 for noting file1 increased /dev/sda2, 1 for noting file2 increases space in the myimage filesystem which itself is stored in /dev/sda2."
}
```

---

## Question 8a [1 point]

(a) What instruction is used to call a function?

```json
{
  "problem_id": "8a",
  "points": 1,
  "type": "Freeform",
  "tags": ["assembly", "x86-64"],
  "answer": "call",
  "llm_judge_instructions": "Award 1 point for identifying the call instruction."
}
```

---

## Question 8b [1 point]

(b) What instruction is used to make a system call?

```json
{
  "problem_id": "8b",
  "points": 1,
  "type": "Freeform",
  "tags": ["assembly", "x86-64"],
  "answer": "syscall",
  "llm_judge_instructions": "Award 1 point for identifying the syscall instruction."
}
```

---

## Question 9 [1 point]

It is a common convention to follow a call to execve() with a message output to standard error. What is the purpose of such a message?

```json
{
  "problem_id": "9",
  "points": 1,
  "type": "Freeform",
  "tags": ["execve"],
  "answer": "If execve succeeds, the current program is replaced; if control continues, execve failed, so printing an error helps diagnose failure.",
  "llm_judge_instructions": "Award 1 point for explaining that the message indicates execve failure if execution continues."
}
```

---

## Question 10a [1 point]

(a) How many bytes can be read from X?

```json
{
  "problem_id": "10a",
  "points": 1,
  "type": "Freeform",
  "tags": ["lseek", "files"],
  "answer": "1049600 bytes (2,097,152? [Note: match to provided solution: 2^20 + 1024 = 1,048,576 + 1,024 = 1,049,600])",
  "llm_judge_instructions": "Award 1 point for the computed value 1,049,600 bytes."
}
```

---

## Question 10b [1 point]

(b) How many data blocks does the file use on disk? Assume each data block can hold 4096 bytes.

```json
{
  "problem_id": "10b",
  "points": 1,
  "type": "Freeform",
  "tags": ["filesystem"],
  "answer": "one data block",
  "llm_judge_instructions": "Award 1 point for recognizing 1 data block is used."
}
```

---

## Question 10c [1 point]

(c) For this file, which is larger, its logical or physical size?

```json
{
  "problem_id": "10c",
  "points": 1,
  "type": "Freeform",
  "tags": ["filesystem"],
  "answer": "logical",
  "llm_judge_instructions": "Award 1 point for identifying logical size is larger."
}
```

---

## Question 10d [1 point]

(d) Does X have a “hole”? Yes or no.

```json
{
  "problem_id": "10d",
  "points": 1,
  "type": "Freeform",
  "tags": ["filesystem"],
  "answer": "yes",
  "llm_judge_instructions": "Award 1 point for recognizing a hole exists."
}
```

---

## Question 11 [2 point(s)]

In the confined environment, nano needs files from /lib/terminfo to function properly, while bash can function properly without these files. Why does nano need them and bash does not?

```json
{
  "problem_id": "11",
  "points": 2,
  "type": "Freeform",
  "tags": ["terminfo", "terminal-control"],
  "answer": "Nano uses full-screen terminal control which requires terminal capability information, provided by terminfos; Bash prints text and does not need terminal control data.",
  "llm_judge_instructions": "Award 2 points: 1 for recognizing nano requires terminal info for full-screen control, 1 for recognizing bash does not need such control."
}
```

---

## Question 12a [2 points]

(a) Can your account validate passwords without having extra privileges? Why?

```json
{
  "problem_id": "12a",
  "points": 2,
  "type": "Freeform",
  "tags": ["security", "passwords"],
  "answer": "Yes; because /etc/shadow can be read by processes in the shadow group.",
  "llm_judge_instructions": "Award 2 points: 1 for password validation capability, 1 for reason related to /etc/shadow permissions."
}
```

---

## Question 12b [2 points]

(b) Can your account delete another user account? Why?

```json
{
  "problem_id": "12b",
  "points": 2,
  "type": "Freeform",
  "tags": ["security", "permissions"],
  "answer": "No; members of the shadow group cannot modify /etc/shadow or /etc/passwd, and they can't delete a directory in /home, which require root privileges.",
  "llm_judge_instructions": "Award 2 points: 1 for inability to delete accounts, 1 for reason related to required root privileges."
}
```

---

## Question 13 [2 points]

Is it safe to give full access to system devices in a confined environment? Why or why not?

```json
{
  "problem_id": "13",
  "points": 2,
  "type": "Freeform",
  "tags": ["security", "devices"],
  "answer": "No; it could grant access to critical devices (e.g., the root filesystem), enabling mounting and modification of files.",
  "llm_judge_instructions": "Award 2 points: 1 for safety concern, 1 for reason involving critical devices."
}
```

---

## Question 14a [1 point]

(a) printf

```json
{
  "problem_id": "14a",
  "points": 1,
  "type": "Freeform",
  "tags": ["kernel-modules"],
  "answer": "no",
  "llm_judge_instructions": "Award 1 point for recognizing printf cannot be used in kernel space."
}
```

---

## Question 14b [1 point]

(b) snprintf

```json
{
  "problem_id": "14b",
  "points": 1,
  "type": "Freeform",
  "tags": ["kernel-modules"],
  "answer": "yes",
  "llm_judge_instructions": "Award 1 point for recognizing snprintf can be used in kernel space."
}
```

---

## Question 14c [1 point]

(c) put_user

```json
{
  "problem_id": "14c",
  "points": 1,
  "type": "Freeform",
  "tags": ["kernel-modules"],
  "answer": "yes",
  "llm_judge_instructions": "Award 1 point for recognizing put_user (putuser) can be used in kernel space."
}
```

---

## Question 14d [1 point]

(d) getpid

```json
{
  "problem_id": "14d",
  "points": 1,
  "type": "Freeform",
  "tags": ["kernel-modules"],
  "answer": "no",
  "llm_judge_instructions": "Award 1 point for recognizing getpid cannot be used in kernel space."
}
```

---

## Question 15 [2 points]

After the c3000procreport module is loaded, does its code run continuously until it is unloaded? Why or why not?

```json
{
  "problem_id": "15",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-modules"],
  "answer": "No; code runs in response to registered events; modules add code but don’t create a separate execution context.",
  "llm_judge_instructions": "Award 2 points: 1 for event-driven execution, 1 for explanation about module behavior."
}
```

---

## Question 16 [2 points]

In the kernel source, current is a pointer to the task that made the system call that the kernel is currently handling. Does this pointer contain a virtual or a physical address? Explain briefly.

```json
{
  "problem_id": "16",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-memory"],
  "answer": "Virtual address",
  "llm_judge_instructions": "Award 2 points: 1 for identifying virtual address; 1 for brief explanation about kernel pointer addressing."
}
```

---

## Question 17a [1 point]

(a) Can abpftracescript be used to monitor calls to puts() made by 3000shell2.c?

```json
{
  "problem_id": "17a",
  "points": 1,
  "type": "Freeform",
  "tags": ["tracing", "bpf"],
  "answer": "Yes",
  "llm_judge_instructions": "Award 1 point for Yes."
}
```

---

## Question 17b [1 point]

(b) Can abpftracescript be used to monitor calls to procreport read() in c3000procreport.c?

```json
{
  "problem_id": "17b",
  "points": 1,
  "type": "Freeform",
  "tags": ["tracing", "bpf"],
  "answer": "Yes",
  "llm_judge_instructions": "Award 1 point for Yes."
}
```

---

## Question 17c [1 point]

(c) Can abpftracescript be used to monitor write system calls made by 3000shell2.c?

```json
{
  "problem_id": "17c",
  "points": 1,
  "type": "Freeform",
  "tags": ["tracing", "bpf"],
  "answer": "Yes",
  "llm_judge_instructions": "Award 1 point for Yes."
}
```

---

## Question 18 [2 points]

When /dev/procreport is closed, what function in c3000procreport.c is called? How can you confirm this?

```json
{
  "problem_id": "18",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-modules"],
  "answer": "procreportrelease() is called; confirm by adding a printk to log or by watching watchprocreport.bt during open/pause/close.",
  "llm_judge_instructions": "Award 2 points: 1 for naming procreportrelease(), 1 for describing a validation method (kernel logs or watchscript)."
}
```

---

## Question 19 [2 points]

What special steps must a kernel module take before writing data to a userspace pointer? What happens in the class VM if you don’t take these steps?

```json
{
  "problem_id": "19",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-memory", "userspace"],
  "answer": "Use proper access methods (e.g., put_user/copy_to_user) to access user-space memory; otherwise, kernel oops occurs.",
  "llm_judge_instructions": "Award 2 points: 1 for mentioning the need to use safe access macros/functions, 1 for describing potential kernel oops or fault if not done."
}
```

---

## Question 20 [2 points]

What is one function we can use to dynamically allocate memory in a kernel module? Why can’t we just use malloc()?

```json
{
  "problem_id": "20",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-memory", "allocation"],
  "answer": "get_free_page() is one; malloc() cannot be used in the kernel because it relies on user-space system calls like mmap/sbrk.",
  "llm_judge_instructions": "Award 2 points: 1 for naming a kernel allocation function, 1 for explaining why malloc() isn’t suitable in the kernel."
}
```

---

## Question 21 [2 points]

What process’s parent is always itself? Is this process special in any other way?

```json
{
  "problem_id": "21",
  "points": 2,
  "type": "Freeform",
  "tags": ["process-management"],
  "answer": "PID 1 (init); it is the first process to run and becomes the parent of any process without a parent.",
  "llm_judge_instructions": "Award 2 points: 1 for identifying PID 1, 1 for explaining its special role as the initial process and parent of orphaned processes."
}
```

---

## Question 22 [2 points]

Does the hardware running the class VM have three, four, or five level page tables? How do you know?

```json
{
  "problem_id": "22",
  "points": 2,
  "type": "Freeform",
  "tags": ["paging", "virtual-memory"],
  "answer": "Four level page tables; pgd and p4d are identical; five levels are not required for the RAM size described.",
  "llm_judge_instructions": "Award 2 points: 1 for noting four levels, 1 for brief justification referencing pgd/p4d behavior."
}
```

---

## Question 23 [2 points]

What is a C statement or declaration that could have generated the following assembly language code? Explain how each line is accounted for in your C code.

.LC0:
.string  "alpha"
.LC1:
.string  "beta"
.LC2:
.string  "gamma"
animals:
.quad    .LC0
.quad    .LC1
.quad    0
.quad    .LC2

```json
{
  "problem_id": "23",
  "points": 2,
  "type": "Freeform",
  "tags": ["c", "assembly"],
  "answer": "char* animals[] = {\"alpha\", \"beta\", NULL, \"gamma\"};",
  "llm_judge_instructions": "Award 2 points: 1 for recognizing the strings, 1 for the animals array containing pointers to those strings and a NULL entry for the middle element."
}
```

---

## Question 24a [2 points]

24a. What part of the C code does this assembly code implement? Be specific.

```json
{
  "problem_id": "24a",
  "points": 2,
  "type": "Freeform",
  "tags": ["assembly", "c"],
  "answer": "This code implements the core of the if statement, comparing g with the number. The cmpl compares the two values; the jg/jge control flow branches implement the Higher/Got It/Lower paths, and the subsequent code outputs the appropriate string and returns -1 via eax.",
  "llm_judge_instructions": "Award 2 points: 1 for identifying comparison of g with the_number and the conditional branches; 1 for explaining the resulting puts/return behavior."
}
```

---

## Question 24b [2 points]

24b. Could the compiler have replaced the reference to the number with the number 42? Why or why not?

```json
{
  "problem_id": "24b",
  "points": 2,
  "type": "Freeform",
  "tags": ["compiler", "optimization"],
  "answer": "No; because the_number may be modified elsewhere in the program, substituting 42 would change semantics.",
  "llm_judge_instructions": "Award 2 points: 1 for noting potential modification of the_number, 1 for explaining that constant-folding would alter behavior if the variable changes."
}
```

---

## Question 25 [2 points]

How could you execve /bin/ls, giving it the command line argument of “-l /home”? Assume that you can use environ for the environment. Be sure to specify the exact arguments you would give to execve, defining any necessary data structures using C code.

```json
{
  "problem_id": "25",
  "points": 2,
  "type": "Freeform",
  "tags": ["execve", "process-management"],
  "answer": "char* myargv[] = {\"ls\", \"-l\", \"/home\", NULL}; execve(\"/bin/ls\", myargv, environ);",
  "llm_judge_instructions": "Award 2 points: 1 for argv array correctly including program name and arguments, 1 for proper use of environ as the environment pointer in execve."
}
```

---

## Question 26 [2 points]

How could you make a program “setuid student”? What privileges would such a program have that it otherwise wouldn’t?

```json
{
  "problem_id": "26",
  "points": 2,
  "type": "Freeform",
  "tags": ["security", "privilege"],
  "answer": "Change ownership to student and set the setuid bit (chown and chmod u+s). The program would have the privileges of the student (access to their files) and could signal their processes, even when run by others.",
  "llm_judge_instructions": "Award 2 points: 1 for describing setuid setup, 1 for explaining privilege expansion to the student’s permissions."
}
```

---

## Question 27 [2 points]

If 3000shell2 is setuid root, does it ever give up its root privileges? If so, when? If not, what are the security implications of this?

```json
{
  "problem_id": "27",
  "points": 2,
  "type": "Freeform",
  "tags": ["security", "privilege"],
  "answer": "Yes, just before running an external command; it drops root privileges by changing effective gid/uid to real ones via become, unless explicitly prevented.",
  "llm_judge_instructions": "Award 2 points: 1 for noting privilege dropping before external commands, 1 for explaining security implications of keeping or dropping privileges."
}
```

---

## Question 28 [2 points]

In bash, if I type “ls > logfile”, what program closes logfile, bash or ls? Why?

```json
{
  "problem_id": "28",
  "points": 2,
  "type": "Freeform",
  "tags": ["redirection", "bash"],
  "answer": "ls closes logfile; bash opens it initially but hands off stdout to ls, so when ls finishes, the file is closed.",
  "llm_judge_instructions": "Award 2 points: 1 for identifying that ls closes the log file, 1 for explaining the redirection and handoff of stdout."
}
```