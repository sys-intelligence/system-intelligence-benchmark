# COMP 3000A: Operating Systems Fall 2021 Final

```json
{
  "exam_id": "comp3000_fall_2021_final",
  "test_paper_name": "COMP 3000A: Operating Systems Fall 2021 Final",
  "course": "COMP 3000",
  "institution": "Carleton University",
  "year": 2021,
  "score_total": 42,
  "num_questions": 21
}
```

---

## Question 1 [2 point(s)]

How does /dev/null behave like a regular file? How is it different?

```json
{
  "problem_id": "1",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "devices"],
  "answer": "You can open, read from, and write to it, just like a regular file.  Unlike a regular file, data written cannot be read back, as reads always return nothing (a read of zero bytes).",
  "llm_judge_instructions": "Award 2 points for correctly describing that /dev/null supports open/read/write like a regular file and that reads return 0 bytes (nothing is readable) and writes discard data; award 1 point for mentioning either the write-discard behavior or the read-empty behavior but not both; award 0 points otherwise."
}
```

---

## Question 2 [2 point(s)]

What is a C statement or declaration that could have generated the following assembly language code?
How do you know? Explain briefly.
.LC0:
.string "Hello world!\n"
...
leaq    .LC0(%rip), %rdi
call    puts@PLT

```json
{
  "problem_id": "2",
  "points": 2,
  "type": "Freeform",
  "tags": ["c", "assembly", "compilers"],
  "answer": "A puts(\"Hello world!\\n\"); or printf(\"Hello world!\\n\"); could have generated this because the compiler can replace simple printf() calls with puts() ones. .LC0 labels the constant hello world string, and the leaq instruction loads this address into the rdi register, which is used for the first integer/address parameter passed to a function. The call instruction then calls puts().",
  "llm_judge_instructions": "Award 2 points for identifying a candidate C statement such as puts(\"Hello world!\\n\"); or printf(\"Hello world!\\n\"); and mentioning that the .LC0 string is the literal, that leaq loads the address into the first argument register, and the call to puts() invokes the function. Award 1 point for naming puts() (or printf()) without the supporting rationale; 0 points otherwise."
}
```

---

## Question 3 [2 point(s)]

On x86-64 systems, which is larger, a process’s virtual address space or a host computer’s physical address space?  How does this affect which part of a process’s address space can be accessed without generating an error?

```json
{
  "problem_id": "3",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtual-memory", "address-space"],
  "answer": "A process’s virtual address space is much larger than the physical address space, because regular computers aren’t close to having 2^64 bytes of RAM. This means that only a small fraction of a process’s (virtual) address space can be accessed without generating an error, because only a small portion can possibly map to allocated physical memory.",
  "llm_judge_instructions": "Award 2 points for stating that virtual space is larger than physical RAM and that only a small portion can be mapped to physical memory; award 1 point for mentioning that most of the virtual space is not backed by physical memory; 0 points otherwise."
}
```

---

## Question 4 [2 point(s)]

Describe how environment variable data is arranged in memory. What C data types are used? How are the key-value pairs stored?

```json
{
  "problem_id": "4",
  "points": 2,
  "type": "Freeform",
  "tags": ["environment-variables"],
  "answer": "Environment variables are arranged as an array of pointers to arrays of characters, with the array of pointers and each array of characters being null terminated (terminated by a 0 value byte) and the array of string pointers is terminated by NULL (a pointer value of 0). Each array of characters (each string) contains the name of an environment variable (the key), an equal sign, and the variable’s value, with that value being ended by a null byte.",
  "llm_judge_instructions": "Award 2 points for describing the array-of-char-pointers structure ending with NULL, and for mentioning each string has 'KEY=VALUE' with a terminating null byte; award 1 point for partial description (e.g., only the array-of-pointers or only null-termination) and 0 otherwise."
}
```

---

## Question 5 [2 point(s)]

You’re writing a program on a new version of Linux that has a new system call,fastread.  Libraries have not been updated to supportfastread.  Can you make a pure, standards-compliant C program that calls thefastreadsystem call? Why or why not?

```json
{
  "problem_id": "5",
  "points": 2,
  "type": "Freeform",
  "tags": ["system-calls", "linux"],
  "answer": "You can’t make a standards-compliant C program because calling system calls requires using platform-specific code (i.e., special assembly language instructions). You have to use inline assembly or a function that has inline assembly (i.e., syscall()).",
  "llm_judge_instructions": "Award 2 points if the answer correctly states that system calls require non-portable, platform-specific code; 1 point for mentioning the need for inline assembly or a wrapper; 0 points otherwise."
}
```

---

## Question 6 [2 point(s)]

Which is biggeron disk, a statically-linked binary or a dynamically-linked binary? Why?

```json
{
  "problem_id": "6",
  "points": 2,
  "type": "Freeform",
  "tags": ["linking", "binaries"],
  "answer": "Statically-linked binaries are bigger on disk because they must include all library code in them. Dynamically-linked binaries can load library code at runtime, thus reducing the size of the binary.",
  "llm_judge_instructions": "Award 2 points for stating that static binaries are larger due to embedded libraries; 1 point for mentioning dynamic linking reduces disk size; 0 otherwise."
}
```

---

## Question 7 [2 point(s)]

In the Microsoft Win32 API, theCreateFile()call is used to open a new or existing file. It returns an object handle (a pointer to a pointer that then refers to the object). What is the Linux system call equivalent to this? What is the type of its return value?

```json
{
  "problem_id": "7",
  "points": 2,
  "type": "Freeform",
  "tags": ["linux", "system-calls", "open"],
  "answer": "The Linux equivalent is open, and it returns a file handle, which is an integer.",
  "llm_judge_instructions": "Award 2 points for identifying 'open' as the Linux analogue and 'int' as the return type; 1 point for partial (e.g., naming open but not the return type); 0 otherwise."
}
```

---

## Question 8 [2 point(s)]

When process A writes to a an existing file X, it freezes/locks up. Why could this happen? How could you get A to continue running? Assume that writes to most other files (new and old) work as expected.

```json
{
  "problem_id": "8",
  "points": 2,
  "type": "Freeform",
  "tags": ["ipc", "files"],
  "answer": "The file could be a named pipe, and the way to fix it would be for another process to read from the pipe.",
  "llm_judge_instructions": "Award 2 points for identifying a named pipe as a possible cause and that another process should read from it; 1 point for mentioning a pipe in general or a blocking I/O scenario; 0 otherwise."
}
```

---

## Question 9 [2 point(s)]

What is the purpose ofqueue nonfullin Tutorial 8’s 3000pc-rendezvous-timeout.c? Explain how it is being used in every place it is accessed in the program, outside of its initialization.

```json
{
  "problem_id": "9",
  "points": 2,
  "type": "Freeform",
  "tags": ["pthreads", "concurrency"],
  "answer": "Its purpose is to allow the consumer to wake up the producer after the producer has gone to sleep. The producer will sleep when the queue is full, meaning there is no room for new production. On line 163 in pthread condtimedwait() is where the producer sleeps, and line 275 is where the consumer uses this variable to wake up the producer.",
  "llm_judge_instructions": "Award 2 points for correctly describing the wake-up mechanism via a condition variable and the producer-consumer interaction; 1 point for partial description focusing on either the sleep or wake-up aspect; 0 otherwise."
}
```

---

## Question 10 [2 point(s)]

What part of3000makefs.sh(from Assignment 3) is necessary to allow ps to work correctly? Why?

```json
{
  "problem_id": "10",
  "points": 2,
  "type": "Freeform",
  "tags": ["procfs", "filesystem"],
  "answer": "Line 58, the mounting of /proc, is necessary for ps to work because ps looks in /proc to get information on running processes.",
  "llm_judge_instructions": "Award 2 points for identifying mounting /proc as necessary for ps to obtain process information; award 1 point for partially correct answers that mention /proc or process information without explicitly stating that /proc must be mounted; award 0 points otherwise."
}
```

---

## Question 11 [2 point(s)]

In the chrooted environment created by3000makefs.sh, doeslsdepend on any dynamically linked libraries? Explain.

```json
{
  "problem_id": "11",
  "points": 2,
  "type": "Freeform",
  "tags": ["chroot", "static-linking"],
  "answer": "No, because it is part of busybox, and busybox is statically linked.",
  "llm_judge_instructions": "Award 2 points for noting static linking or busybox; 1 point for partial mention of static linking; 0 otherwise."
}
```

---

## Question 12 [2 point(s)]

Can a mount command increase the space available for storing files?  Explain.  (Be sure to consider uses beyond those in3000makefs.sh.)

```json
{
  "problem_id": "12",
  "points": 2,
  "type": "Freeform",
  "tags": ["mount", "filesystem"],
  "answer": "Yes, because you can mount a filesystem on an additional device, such as a USB stick. This storage thus becomes available to files created under the mountpoint.",
  "llm_judge_instructions": "Award 2 points for stating that mounting additional storage increases available space under the mount point; 1 point for partial reasoning; 0 otherwise."
}
```

---

## Question 13 [2 point(s)]

On the class VM, what files have to be changed in order to add a new user? What about to add a group?

```json
{
  "problem_id": "13",
  "points": 2,
  "type": "Freeform",
  "tags": ["linux-users", "files"],
  "answer": "You change /etc/passwd and /etc/shadow to add a new user, and /etc/group and /etc/gshadow to add a group.",
  "llm_judge_instructions": "Award 2 points for listing /etc/passwd and /etc/shadow for adding a user and /etc/group and /etc/gshadow for adding a group; award 1 point for partially listing two of the required files (e.g., passwd and shadow or group and gshadow); award 0 points otherwise."
}
```

---

## Question 14 [2 point(s)]

3000shellcan make many stat system calls for every command entered.  Which function makes these stat calls? What are these stat calls for?

```json
{
  "problem_id": "14",
  "points": 2,
  "type": "Freeform",
  "tags": ["filesystem", "stat"],
  "answer": "findbinary() makes these calls (on line 124). They check whether the constructed absolute filename actually exists or not, thus telling us whether we’ve found the executable we are looking for.",
  "llm_judge_instructions": "Award 2 points for identifying the function and the purpose (existence check for executables); 1 point for partial identification; 0 otherwise."
}
```

---

## Question 15 [2 point(s)]

If you do a printf() that does not end in a newline, it will not be immediately output to a terminal; instead, it will only be output later once a newline is output.  How can you force terminal output without a newline?
Why does this work?

```json
{
  "problem_id": "15",
  "points": 2,
  "type": "Freeform",
  "tags": ["stdio", "buffering"],
  "answer": "You can force output with fflush(), because C library functions such as printf() do buffered output to terminals and so only issue write system calls when their buffer is filled, a newline is output, or the buffer is flushed.",
  "llm_judge_instructions": "Award 2 points for mentioning fflush() and the reason about buffering; 1 point for mentioning an explicit flush or a partial buffering concept; 0 points otherwise."
}
```

---

## Question 16 [2 point(s)]

What is the relationship between sigaction() and kill()?

```json
{
  "problem_id": "16",
  "points": 2,
  "type": "Freeform",
  "tags": ["signals"],
  "answer": "sigaction() is used to register signal handlers which are run when a process receives a signal. kill() is used to send signals.",
  "llm_judge_instructions": "Award 2 points for correctly describing registration of handlers with sigaction and sending signals with kill; 0 otherwise."
}
```

---

## Question 17 [2 point(s)]

Tools likegdbandstrace, that use the ptrace system call, have several significant limitations compared tobpftraceand other tools based on eBPF.
What is one thing you can do with eBPF that you can’t do with ptrace? And, what key restriction is placed on eBPF programs that isn’t there for ptrace programs?

```json
{
  "problem_id": "17",
  "points": 2,
  "type": "Freeform",
  "tags": ["ebpf", "ptrace"],
  "answer": "With eBPF you can observe all the processes on the system and change how the kernel works, potentially modifying how security or even scheduling decisions are made; ptrace can only allow one process to be observed at a time. eBPF programs must be loaded and run by privileged users and are verified by the kernel's verifier.",
  "llm_judge_instructions": "Award 2 points for stating both a system-wide observability/kernel interaction capability of eBPF (versus ptrace's one-at-a-time limitation) and mentioning that eBPF programs must be loaded by privileged users and are restricted by the kernel verifier; award 1 point for partial accuracy; 0 points otherwise."
}
```

---

## Question 18 [2 point(s)]

What is one signal that can be sent directly from one process to another (via the kernel)? What is another signal that is sent by the kernel itself and received by a process? Briefly explain the purpose of each signal.

```json
{
  "problem_id": "18",
  "points": 2,
  "type": "Freeform",
  "tags": ["signals"],
  "answer": "Many possible answers.  Common ones are SIGTERM, SIGKILL, and SIGSTOP for sending from one process to another.  SIGSEGV, SIGBUS, SIGCHLD and such are sent by the kernel to a process. (Should also briefly explain each signal.)",
  "llm_judge_instructions": "Award 2 points for correctly distinguishing at least one user-sent signal (with brief purpose) and at least one kernel-sent signal (with brief purpose); 1 point for partial accuracy; 0 points otherwise."
}
```

---

## Question 19 [2 point(s)]

Could you make a special file that, when read, returns a random sentence?  Why or why not?  Be sure to explain how it could be done or why it would be impossible. (No code is required in your answer.)

```json
{
  "problem_id": "19",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-module", "character-device"],
  "answer": "Yes you could, it would just be a kernel module like newgetpid, but it would choose a random sentence from a built-in database (or perhaps load it previously) and then return it. It is a character device because input and output can be arbitrarily sized; with block devices, we can only read or write entire blocks (i.e., only 4K at a time).",
  "llm_judge_instructions": "Award 2 points for describing a kernel module implementing a character device that returns random sentences; 1 point for partial hardware/driver reasoning; 0 otherwise."
}
```

---

## Question 20 [2 point(s)]

After  loading  theonesmodule  from  Tutorial  7,  running  “cat  /dev/ones”  will  produce  an  unbounded sequence of 1’s.  How is this possible, given that ones read() only outputs a limited number of 1’s?  Explain briefly.

```json
{
  "problem_id": "20",
  "points": 2,
  "type": "Freeform",
  "tags": ["devices", "read"],
  "answer": "On every read, it will fill the given buffer completely and return the size of the buffer as the number of characters read. Thus there’s never any indication of end of file (and indeed the offset is never changed), so subsequent reads will be indicated and will return the same, thus producing unbounded output.",
  "llm_judge_instructions": "Award 2 points for describing buffer-full reads and lack of EOF behavior leading to repeated outputs; 1 point for partial explanation; 0 points otherwise."
}
```

---

## Question 21 [2 point(s)]

If the kernel accesses a process’s data using standard C methods, such as dereferencing a pointer, it can result in errors. Why? How can it access process data safely?

```json
{
  "problem_id": "21",
  "points": 2,
  "type": "Freeform",
  "tags": ["kernel-space", "user-space"],
  "answer": "User data is in a process with its own address space separate from the kernel (on most architectures), meaning that userspace pointers simply aren’t valid in the context of the kernel’s own address space. Further, it is possible a userspace pointer is pointing to memory that hasn’t been loaded or isn’t allocated memory; the kernel must check and handle such conditions. To access userspace pointers safely, the kernel uses special functions such as get_user() and put_user() that do the necessary translations.",
  "llm_judge_instructions": "Award 2 points for mentioning separate address spaces and using safe access helpers (get_user/put_user); 1 point for partial reasoning; 0 points otherwise."
}
```