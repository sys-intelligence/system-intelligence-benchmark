# Lab 3a: Demand Paging

## Environment

You are working in the PKU Pintos environment. The codebase is located at `/home/PKUOS/pintos`.

**Build directory**: `src/vm` (this enables the `-DVM` flag)

**Protected files** (do not modify):
- `src/tests/userprog/*`, `src/tests/vm/*`, `src/tests/filesys/base/*`
- `src/vm/Make.vars`, `src/tests/Make.tests`

**Files you should modify**:
- `src/vm/frame.c`, `src/vm/frame.h` - Frame table implementation
- `src/vm/page.c`, `src/vm/page.h` - Supplemental page table
- `src/vm/swap.c`, `src/vm/swap.h` - Swap table implementation
- `src/userprog/process.c` - Modify `load_segment()` for lazy loading
- `src/userprog/exception.c` - Page fault handler
- `src/userprog/syscall.c` - Handle page faults during syscalls
- `src/threads/thread.c`, `src/threads/thread.h` - Per-thread page table info
- `src/threads/init.c` - Initialization
- `src/Makefile.build` - Add VM source files to compilation

---

## Overview

By now you should have some familiarity with the inner workings of Pintos. Your OS can properly handle multiple threads of execution with proper synchronization, and can load multiple user programs at once. However, the number and size of programs that can run is limited by the machine's main memory size. In this assignment, you will remove that limitation.

**You will build this assignment on top of Lab 2.** Test programs from Lab 2 should also work with Lab 3. You should take care to fix any bugs in your Lab 2 code before you start work on Lab 3, because those bugs will most likely cause the same problems in Lab 3.

---

## Tests Required

**Here are all the tests you need to pass:**

1. **All tests in** `tests/userprog`
2. **All tests in** `tests/filesys/base`
3. **Part of the tests in** `tests/vm`:
   - page-linear
   - page-parallel
   - page-shuffle
   - page-merge-seq
   - page-merge-par
   - pt-bad-addr
   - pt-bad-read
   - pt-write-code
   - pt-write-code2
   - pt-grow-bad

---

## Your Tasks

**This assignment is an open-ended design problem.** We are going to say as little as possible about how to do things. Instead we will focus on what functionality we require your OS to support. We will expect you to come up with a design that makes sense. You will have the freedom to choose how to handle page faults, how to organize the swap partition, how to implement paging, etc.

### Task 1: Paging

#### Exercise 1.1: Implement Paging for Executable Segments

**Implement paging for segments loaded from executables.**

- All of these pages should be loaded **lazily**, that is, only as the kernel intercepts page faults for them.
- Upon eviction:
  - Pages **modified** since load (e.g. as indicated by the "dirty bit") should **be written to swap**.
  - **Unmodified** pages, including read-only pages, should **never be written to swap** because they can always be read back from the executable.

#### Exercise 1.2: Implement Page Replacement

**Implement a global page replacement algorithm that approximates LRU.**

- Your algorithm should perform **at least as well as** the simple variant of the "second chance" or "clock" algorithm.

**Your design should allow for parallelism.** If one page fault requires I/O, in the meantime processes that do not fault should continue executing and other page faults that do not require I/O should be able to complete. This will require some **synchronization** effort.

**You'll need to modify the core of the program loader**, which is the loop in **`load_segment()`** in `userprog/process.c`.

- Each time around the loop, **`page_read_bytes`** receives the number of bytes to read from the executable file and **`page_zero_bytes`** receives the number of bytes to initialize to zero following the bytes read. **The two always sum to `PGSIZE` (4,096).** The handling of a page depends on these variables' values:
- If `page_read_bytes` equals `PGSIZE`, the page should be demand paged from the underlying file on its first access.
- If `page_zero_bytes` equals `PGSIZE`, the page does not need to be read from disk at all because it is all zeroes. You should handle such pages by **creating a new page consisting of all zeroes at the first page fault**.
- Otherwise, neither `page_read_bytes` nor `page_zero_bytes` equals `PGSIZE`. In this case, an initial part of the page is to be read from the underlying file and the remainder zeroed.

**Hint**: In order for demand paging to work, you need to record metadata for each lazily-loaded page, which allows you to know what location to read its content from disk later. In particular, if before demand paging a page's content comes from reading offset `X` of the executable file at loading time, after demand paging, you should still read the content from offset `X` of the executable file during page fault handling. **The supplementary page table keeps track of relationship of memory pages and their backing store locations.** You should consider filling in the supplementary page table in `load_segment`.

**Tip**: If you would like to retain the previous file-reading code in `load_segment`, you can use macros like this to select the behavior at compilation time:

```c
static bool load_segment(...)
{
#ifndef VM
  file_seek (file, ofs);
  ...
#else
  ... // fill in code for demand paging behavior in lab 3.
#endif
}
```

If you compile Pintos under lab 1 (`threads` directory) or lab 2 (`userprog` directory), the `#ifndef VM` section will be selected. If you compile Pintos under lab 3 or lab 4, the `#else` section will be selected.

**Tip**: You can use the `-ul` kernel command-line option to limit the size of the user pool, which makes it easy to test your VM implementation with various user memory sizes. For example:
```
pintos --swap-size=2 --filesys-size=2 -p ../../examples/echo -a echo -- -ul=4 -f -q run 'echo hello world'
```
will test Pintos with 4 page frames for user program.

---

### Task 2: Accessing User Memory

#### Exercise 2.1: Handle Page Faults in System Calls

**Adjust user memory access code in system call handling to deal with potential page faults.**

You will need to adapt your code to access user memory while handling a system call.

- Just as user processes may access pages whose content is currently in a file or in swap space, so can they pass addresses that refer to such non-resident pages to system calls.
- Moreover, unless your kernel takes measures to prevent this, a page may be evicted from its frame even while it is being accessed by kernel code. If kernel code accesses such non-resident user pages, a page fault will result.

**While accessing user memory, your kernel must either be prepared to handle such page faults, or it must prevent them from occurring.**

- The kernel must prevent such page faults while it is **holding resources** it would need to acquire to handle these faults.
- In Pintos, **such resources include locks acquired by the device driver(s)** that control the device(s) containing the file system and swap space.
- As a concrete example, you must not allow page faults to occur while a device driver accesses a user buffer passed to `file_read`, because you would not be able to invoke the driver while handling such faults.

**Preventing such page faults requires cooperation between the code within which the access occurs and your page eviction code.**

- For instance, you could extend your frame table to record when a page contained in a frame must not be evicted. (This is also referred to as "**pinning**" or "**locking**" the page in its frame.)
- Pinning restricts your page replacement algorithm's choices when looking for pages to evict, so be sure to pin pages no longer than necessary, and avoid pinning pages when it is not necessary.

---

## Building and Testing

Build in the `vm/` directory:
```bash
cd /home/PKUOS/pintos/src/vm
make
```

Run all tests:
```bash
cd build
make check
```
