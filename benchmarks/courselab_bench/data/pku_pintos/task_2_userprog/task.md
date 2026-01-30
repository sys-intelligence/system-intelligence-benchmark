# Lab 2: User Programs

## Environment

You are working in the PKU Pintos environment. The codebase is located at `/home/PKUOS/pintos`.

**Build directory**: `src/userprog`

**Protected files** (do not modify):
- `src/tests/userprog/*`, `src/tests/userprog/no-vm/*`
- `src/userprog/Make.vars`, `src/tests/Make.tests`

**Files you should modify**:
- `src/userprog/process.c`, `src/userprog/process.h` - Process loading and argument passing
- `src/userprog/syscall.c`, `src/userprog/syscall.h` - System call handler
- `src/userprog/exception.c` - Exception handling
- `src/threads/thread.c`, `src/threads/thread.h` - Thread management

---

## Overview

Now that you've worked with Pintos and are becoming familiar with its infrastructure and thread package, it's time to start working on the parts of the system that allow running user programs.

The base code already supports loading and running user programs, but no I/O or interactivity is possible. In this project, you will enable programs to interact with the OS via system calls.

You will be working out of the `userprog/` directory for this assignment, but you will also be interacting with almost every other part of Pintos.

**You can build project 2 on top of your project 1 submission** (dogfooding your own kernel changes like a product). Or **you can start fresh**. **No code from project 1 is required for this assignment.**

---

## Your Tasks

### Task 1: Process Termination Messages

#### Exercise 1.1

**Print exit message** formatted as `"%s: exit(%d)\n"` with **process name** and **exit status** when a user process is terminated.

Whenever a user process terminates, because it called `exit` or for any other reason, print the process's name and exit code, formatted as if printed by `printf ("%s: exit(%d)\n", ...);`.

- The name printed should be **the full name** passed to `process_execute()`, omitting command-line arguments.
- **Do not print these messages when a kernel thread that is not a user process terminates, or when the `halt` system call is invoked.**

---

### Task 2: Argument Passing

#### Exercise 2.1

**Add argument passing support** for `process_execute()`.

Currently, `process_execute()` does not support passing arguments to new processes. Implement this functionality by extending `process_execute()` so that instead of simply taking a program file name as its argument, it divides it into words at spaces.

- The first word is the program name, the second word is the first argument, and so on. That is, `process_execute("grep foo bar")` should run `grep` passing two arguments `foo` and `bar`.
- Within a command line, **multiple spaces are equivalent to a single space**.
- You can impose a reasonable limit on the length of the command line arguments.

**Hint:** You can parse argument strings any way you like. If you're lost, look at `strtok_r()`, prototyped in `lib/string.h`.

---

### Task 3: Accessing User Memory

#### Exercise 3.1

**Support reading from and writing to user memory for system calls.**

As part of a system call, the kernel must often access memory through pointers provided by a user program. **The kernel must be very careful about doing so**, because the user can pass a null pointer, a pointer to unmapped virtual memory, or a pointer to kernel virtual address space (above `PHYS_BASE`).

All of these types of invalid pointers must be rejected without harm to the kernel or other running processes, by **terminating the offending process and freeing its resources**.

**There are at least two reasonable ways to do this correctly:**

1. **Verify the validity of a user-provided pointer, then dereference it.** Look at the functions in `userprog/pagedir.c` and in `threads/vaddr.h`. This is the **simplest** way.

2. **Check only that a user pointer points below `PHYS_BASE`, then dereference it.** An invalid user pointer will cause a "page fault" that you can handle by modifying the code for `page_fault()` in `userprog/exception.c`. This technique is normally **faster** because it takes advantage of the processor's MMU.

In either case, you need to make sure not to "leak" resources. If you encounter an invalid user pointer after acquiring a lock or allocating memory, you must still release the lock or free the memory.

---

### Task 4: System Calls

#### Exercise 4.1

**Implement the system call handler in `userprog/syscall.c`.**

The skeleton implementation we provide "handles" system calls by terminating the process. It will need to **retrieve the system call number**, then **any system call arguments**, and **carry out appropriate actions**.

#### Exercise 4.2

**Implement the following system calls (13 in all for this lab):**

- **`void halt(void)`**: Terminates Pintos by calling `shutdown_power_off()`.

- **`void exit(int status)`**: Terminates the current user program, returning _status_ to the kernel. If the process's parent `wait`s for it, this is the status that will be returned.

- **`pid_t exec(const char *cmd_line)`**: Runs the executable whose name is given in _cmd_line_, passing any given arguments, and returns the new process's program id (pid). Must return pid `-1` if the program cannot load or run. **The parent process cannot return from the `exec` until it knows whether the child process successfully loaded its executable.** Use appropriate synchronization.

- **`int wait(pid_t pid)`**: Waits for a child process _pid_ and retrieves the child's exit status.
  - If _pid_ is still alive, wait until it terminates, then return the status that _pid_ passed to `exit`.
  - If _pid_ did not call `exit()`, but was terminated by the kernel (e.g. killed due to an exception), return `-1`.
  - It is perfectly legal for a parent process to wait for child processes that have already terminated.
  - `wait` must fail and return -1 immediately if: _pid_ does not refer to a direct child, or the process has already called `wait` on _pid_.
  - **All of a process's resources, including its `struct thread`, must be freed** whether its parent ever waits for it or not.

- **`bool create(const char *file, unsigned initial_size)`**: Creates a new file. Returns true if successful.

- **`bool remove(const char *file)`**: Deletes the file. A file may be removed regardless of whether it is open or closed.

- **`int open(const char *file)`**: Opens the file. Returns a nonnegative integer file descriptor, or -1 if the file could not be opened. File descriptors 0 and 1 are reserved for stdin/stdout. **File descriptors are not inherited by child processes.**

- **`int filesize(int fd)`**: Returns the size, in bytes, of the file open as _fd_.

- **`int read(int fd, void *buffer, unsigned size)`**: Reads _size_ bytes from the file open as _fd_ into _buffer_. Returns the number of bytes actually read, or -1 if the file could not be read. **Fd 0 reads from the keyboard using `input_getc()`.**

- **`int write(int fd, const void *buffer, unsigned size)`**: Writes _size_ bytes from _buffer_ to the open file _fd_. Returns the number of bytes actually written. **Fd 1 writes to the console.** Your code to write to the console should write all of _buffer_ in one call to `putbuf()`.

- **`void seek(int fd, unsigned position)`**: Changes the next byte to be read or written in open file _fd_ to _position_.

- **`unsigned tell(int fd)`**: Returns the position of the next byte to be read or written in open file _fd_.

- **`void close(int fd)`**: Closes file descriptor _fd_. **Exiting or terminating a process implicitly closes all its open file descriptors.**

#### Important Notes

- To implement syscalls, you need to provide ways to read and write data in user virtual address space. You need this ability before you can even obtain the system call number.
- **You must synchronize system calls so that any number of user processes can make them at once.** In particular, it is not safe to call into the file system code from multiple threads at once. **Your system call implementation must treat the file system code as a critical section.**
- When you're done with this part, Pintos should be bulletproof. **Nothing that a user program can do should ever cause the OS to crash, panic, fail an assertion, or otherwise malfunction.**

---

### Task 5: Denying Writes to Executables

#### Exercise 5.1

**Add code to deny writes to files in use as executables.**

Many OSes do this because of the unpredictable results if a process tried to run code that was in the midst of being changed on disk.

You can use `file_deny_write()` to prevent writes to an open file. Calling `file_allow_write()` on the file will re-enable them. Closing a file will also re-enable writes. Thus, to deny writes to a process's executable, you must keep it open as long as the process is still running.

---

## Building and Testing

Build in the `userprog/` directory:
```bash
cd /home/PKUOS/pintos/src/userprog
make
```

Run all tests:
```bash
cd build
make check
```
