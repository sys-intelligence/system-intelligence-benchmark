# CS162 Operating Systems and System Programming - Summer 2022 Final Exam

```json
{
  "exam_id": "cs162_operating_systems_and_system_programming_summer_2022_final",
  "test_paper_name": "CS162 Operating Systems and System Programming: Summer 2022 Final Exam",
  "course": "CS162 Operating Systems and System Programming",
  "institution": "UC Berkeley",
  "year": 2022,
  "score_total": 90,
  "num_questions": 26
}
```

---

## Question 1a [2 points]

True or False: In Linux, a user program will terminate if it page faults.

Your answer should be either "True" or "False", followed by a brief explanation (two sentences or less). Longer explanations may get no credit.

```json
{
  "problem_id": "1a",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "virtual-memory", "page-faults"],
  "reference_materials": ["rust_reference.md"],
  "answer": "False. Stack growth and paging out to disk are counterexamples",
  "llm_judge_instructions": "Award 1 point for correctly answering False. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 1b [2 points]

True or False: Regardless of the distribution of job arrival times and job servicing times, queuing delay will grow unboundedly as utilization approaches 1.

Your answer should be either "True" or "False", followed by a brief explanation (two sentences or less). Longer explanations may get no credit.

```json
{
  "problem_id": "1b",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "scheduling", "queuing"],
  "reference_materials": ["rust_reference.md"],
  "answer": "False. Consider constant arrival and service rates",
  "llm_judge_instructions": "Award 1 point for correctly answering False. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 1c [2 points]

True or False: Increasing the amount of physical memory while keeping page size constant will always decrease the number of page faults (assuming we use the same demand paging policy).

Your answer should be either "True" or "False", followed by a brief explanation (two sentences or less). Longer explanations may get no credit.

```json
{
  "problem_id": "1c",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "virtual-memory", "page-faults"],
  "reference_materials": ["rust_reference.md"],
  "answer": "False. FIFO and Belady's anomaly",
  "llm_judge_instructions": "Award 1 point for correctly answering False. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 1d [2 points]

True or False: A program in an unsafe state will deadlock (or crash before doing so).

Your answer should be either "True" or "False", followed by a brief explanation (two sentences or less). Longer explanations may get no credit.

```json
{
  "problem_id": "1d",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "concurrency", "deadlock"],
  "reference_materials": ["rust_reference.md"],
  "answer": "False. Programs don't necessarily acquire all their resources at once.",
  "llm_judge_instructions": "Award 1 point for correctly answering False. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 1e [2 points]

True or False: FAT is slow when reading from a random location in a large file.

Your answer should be either "True" or "False", followed by a brief explanation (two sentences or less). Longer explanations may get no credit.

```json
{
  "problem_id": "1e",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "file-systems", "fat"],
  "reference_materials": ["rust_reference.md"],
  "answer": "True. FAT has linear traversal time as it uses a linked list implementation of files.",
  "llm_judge_instructions": "Award 1 point for correctly answering True. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 1f [2 points]

True or False: Using a buffer cache is an example of demand paging.

Your answer should be either "True" or "False", followed by a brief explanation (two sentences or less). Longer explanations may get no credit.

```json
{
  "problem_id": "1f",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "virtual-memory", "caching"],
  "reference_materials": ["rust_reference.md"],
  "answer": "False. The buffer cache is not the same as demand paging. The buffer cache caches disk blocks in memory; demand paging saves pages of memory to disk.",
  "llm_judge_instructions": "Award 1 point for correctly answering False. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 1g [2 points]

True or False: The function f(x) = x + 1 is idempotent.

Your answer should be either "True" or "False", followed by a brief explanation (two sentences or less). Longer explanations may get no credit.

```json
{
  "problem_id": "1g",
  "points": 2,
  "type": "Freeform",
  "tags": ["distributed-systems", "idempotency"],
  "reference_materials": ["rust_reference.md"],
  "answer": "False. f(f(x)) != f(x)",
  "llm_judge_instructions": "Award 1 point for correctly answering False. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 1h [2 points]

True or False: Compared to single-level page tables, multi-level page tables use less memory for sparse address spaces.

Your answer should be either "True" or "False", followed by a brief explanation (two sentences or less). Longer explanations may get no credit.

```json
{
  "problem_id": "1h",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "virtual-memory", "page-tables"],
  "reference_materials": ["rust_reference.md"],
  "answer": "True. You don't need to allocate every table when the address space is sparse.",
  "llm_judge_instructions": "Award 1 point for correctly answering True. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 2a [2 points]

Which of the following are approximation(s) to MIN? (Select all that apply)

A. Second-chance list

B. Clock

C. FIFO

D. LRU

E. None of the above

Your answer should list all correct letters (e.g., "A, B"), followed by a brief explanation. Longer explanations may get no credit.


```json
{
  "problem_id": "2a",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "virtual-memory", "page-replacement"],
  "reference_materials": ["rust_reference.md"],
  "answer": "A, B, D. LRU approximates MIN, and clock/second-chance approximate LRU.",
  "llm_judge_instructions": "Award 1 point for listing exactly the correct letters that apply. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 2b [2 points]

Which of the following are true about I/O? (Select all that apply)

A. The top half of a device driver polls the bottom half of the device driver.

B. Memory-mapped I/O is an example of direct memory access.

C. In port-mapped I/O, each device port is mapped to a unique location on disk.

D. In programmed I/O, the CPU programs an external controller to do I/O while the CPU can work on other things.

E. None of the above.

Your answer should list all correct letters (e.g., "A, B"), followed by a brief explanation. Longer explanations may get no credit.

```json
{
  "problem_id": "2b",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "io"],
  "reference_materials": ["rust_reference.md"],
  "answer": "E. None of the options are correct. A: Top half and bottom half refer to interrupt-driven I/O; polling is not used. B: Memory-mapped I/O actively involves the CPU; in DMA, an external device writes data to memory independently, then interrupts the CPU when the data is ready. C: Port-mapped I/O does not require involvement of the disk. D: Programmed I/O involves special CPU instructions (eg. in and out), not an external I/O controller.",
  "llm_judge_instructions": "Award 1 point for listing exactly the correct letters that apply. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 2c [2 points]

Which of the following are true about storage devices? (Select all that apply)

A. Sequential reads are faster than random reads in HDDs.

B. Constantly writing and erasing the same memory location will wear out HDDs faster than SSDs.

C. SSDs are generally cheaper than HDDs (for the same amount of storage).

D. Like RAM, storage devices are byte-addressed.

E. None of the above.

Your answer should list all correct letters (e.g., "A, B"), followed by a brief explanation. Longer explanations may get no credit.

```json
{
  "problem_id": "2c",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "storage"],
  "reference_materials": ["rust_reference.md"],
  "answer": "A. A: Sequential reads on HDDs are usually faster than random reads because we only have to wait for the disk to spin under the head. B: SSD pages wear out when they are erased; HDDs do not wear out as quickly. C: SSDs are generally more expensive. D: Storage devices are addressed in units of sectors/pages/blocks.",
  "llm_judge_instructions": "Award 1 point for listing exactly the correct letters that apply. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 2d [2 points]

Which of the following are true about cache misses? (Select all that apply)

A. Coherence misses can occur when multiple processors share a single cache.

B. Conflict misses can be reduced by reducing the number of index bits.

C. Capacity misses grow linearly with the size of the cache.

D. Compulsory misses grow linearly with the size of the cache.

E. None of the above.

Your answer should list all correct letters (e.g., "A, B"), followed by a brief explanation. Longer explanations may get no credit.

```json
{
  "problem_id": "2d",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "caching"],
  "reference_materials": ["rust_reference.md"],
  "answer": "A, B. A: In a multiprocessor system, actions by one processor can invalidate the cache entries for another processor, possibly resulting in a coherence miss. B: A cache with a higher associativity can reduce the number of conflict misses. C: Making a cache larger should decrease the number of capacity misses. D: Compulsory misses occur when a cache line is loaded for the first time; increasing the size of the cache has no effect on the number of compulsory misses.",
  "llm_judge_instructions": "Award 1 point for listing exactly the correct letters that apply. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 2e [2 points]

Which of the following are true about this Rust program? (Select all that apply)

```rust
fn main() {
    let s = "General".to_string();
    let s = "General Kenobi".to_string();
    kenobi(s);
    println!("{}", s);
}

fn kenobi(s: String) {
    if s == "General Kenobi" {
        println!("Hello there");
    }
}
```

A. The program reuses s without declaring s as mutable, which is not allowed.

B. main will error at RUNTIME because it tries to use a variable it does not own.

C. The program will compile if we delete the print statement in main.

D. The program will compile if we replace `kenobi(s: String)` and `kenobi(s)` with `kenobi(s: &str)` and `kenobi(&s)`, respectively.

E. None of the above.

Your answer should list all correct letters (e.g., "A, B"), followed by a brief explanation. Longer explanations may get no credit.

```json
{
  "problem_id": "2e",
  "points": 2,
  "type": "Freeform",
  "tags": ["rust", "ownership"],
  "reference_materials": ["rust_reference.md"],
  "answer": "C, D. A: The second s is a new variable due to the let declaration. It is not a reassignment of the original s. B: This program will result in compile-time, not run-time, errors. C: This solves the issue; s would no longer be used after being moved into kenobi. D: Passing a reference to s also fixes the problem, as ownership of s is not moved into kenobi",
  "llm_judge_instructions": "Award 1 point for listing exactly the correct letters that apply. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 2f [2 points]

Which of the following are true about deadlocks? (Select all that apply)

A. Deadlocks can be provably avoided by defining a global resource acquisition order.

B. Deadlocks can ONLY occur if there is a circular wait for resources.

C. Strict priority schedulers use priority donation to prevent deadlocks.

D. A program in a safe state can eventually deadlock.

E. None of the above.

Your answer should list all correct letters (e.g., "A, B"), followed by a brief explanation. Longer explanations may get no credit.

```json
{
  "problem_id": "2f",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "concurrency", "deadlock"],
  "reference_materials": ["rust_reference.md"],
  "answer": "A, B, D. A: Circular wait is a necessary condition for deadlock. B: Circular wait is a necessary condition for deadlock. C: Priority donation prevents starvation of a high-priority thread; it does not prevent deadlock. D: A safe state means that there is a non-blocking order of threads that allows all threads to complete. Deadlock can still occur starting from a safe state (eg. if the non-blocking ordering is not followed).",
  "llm_judge_instructions": "Award 1 point for listing exactly the correct letters that apply. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 2g [2 points]

Which of the following are true about file numbers (inumbers)? (Select all that apply)

A. A directory is a file containing file name and file number mappings.

B. In FAT, the file number is the index of the first block of a file in the file allocation table.

C. A file number uniquely identifies and locates a file on disk.

D. In FFS, the file number is the index of an inode in the inode array.

E. None of the above.

Your answer should list all correct letters (e.g., "A, B"), followed by a brief explanation. Longer explanations may get no credit.

```json
{
  "problem_id": "2g",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "file-systems"],
  "reference_materials": ["rust_reference.md"],
  "answer": "A, B, C, D. All statements are correct.",
  "llm_judge_instructions": "Award 1 point for listing exactly the correct letters that apply. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 2h [2 points]

Which of the following are optimizations introduced by Berkeley FFS? (Select all that apply)

A. Introducing skip-lanes to the freelist for faster deallocation of used blocks.

B. Using variable-sized extents to accommodate files too large to be stored in an inode-based format.

C. A first-free allocation of new file blocks which yields sequential blocks for large files.

D. Putting a directory and its file into common block groups.

E. None of the above.

Your answer should list all correct letters (e.g., "A, B"), followed by a brief explanation. Longer explanations may get no credit.

```json
{
  "problem_id": "2h",
  "points": 2,
  "type": "Freeform",
  "tags": ["operating-systems", "file-systems", "ffs"],
  "reference_materials": ["rust_reference.md"],
  "answer": "C, D. C: FFS uses first-free allocation for sequential block placement. D: FFS groups directories and their files in common cylinder groups.",
  "llm_judge_instructions": "Award 1 point for listing exactly the correct letters that apply. Award 1 point for a valid explanation. Longer explanations may get no credit."
}
```

---

## Question 3a [3 points]

Explain why the FAT file system does not support hard links.

Please answer in THREE SENTENCES OR LESS. Longer explanations may get no credit

```json
{
  "problem_id": "3a",
  "points": 3,
  "type": "Freeform",
  "tags": ["operating-systems", "file-systems", "fat"],
  "reference_materials": ["rust_reference.md"],
  "answer": "FAT cannot reference count because file metadata is stored in the parent directory.",
  "llm_judge_instructions": "Award full points for a fully correct explanation. award partial credit for partially correct explanations"
}
```

---

## Question 3b [3 points]

What is the relationship between struct file and struct inode in PintOS?

Please answer in THREE SENTENCES OR LESS. Longer explanations may get no credit

```json
{
  "problem_id": "3b",
  "points": 3,
  "type": "Freeform",
  "tags": ["operating-systems", "file-systems", "pintos"],
  "reference_materials": ["rust_reference.md"],
  "answer": "A struct file contains a struct inode. There can be many struct file’s referencing the same struct inode.",
  "llm_judge_instructions": "Award full points for a fully correct explanation. award partial credit for partially correct explanations"
}
```

---

## Question 3c [3 points]

Is port-mapped I/O or DMA preferable for storage devices? Explain.

Please answer in THREE SENTENCES OR LESS. Longer explanations may get no credit

```json
{
  "problem_id": "3c",
  "points": 3,
  "type": "Freeform",
  "tags": ["operating-systems", "io", "dma"],
  "reference_materials": ["rust_reference.md"],
  "answer": "DMA does not require CPU cycles (eg. polling), so it is preferable for disk accesses, which can potentially take millions of CPU cycles.",
  "llm_judge_instructions": "Award full points for a fully correct explanation. award partial credit for partially correct explanations"
}
```

---

## Question 3d [3 points]

Under what conditions can we overlap cache and TLB lookups?

Please answer in THREE SENTENCES OR LESS. Longer explanations may get no credit

```json
{
  "problem_id": "3d",
  "points": 3,
  "type": "Freeform",
  "tags": ["operating-systems", "virtual-memory", "caching", "tlb"],
  "reference_materials": ["rust_reference.md"],
  "answer": "Cache lookups can be overlapped when the page offset in the virtual address contains the cache index. See lecture 15, slide 26.",
  "llm_judge_instructions": "Award full points for a fully correct explanation. award partial credit for partially correct explanations"
}
```

---

## Question 3e [3 points]

Oh no! Darth Vader broke one of his disks and lost his Death Star plans. Luckily, Darth Vader was using RAID 5 and still has the other 4 disks. The contents of these disks are:

- Disk 1: 100010
- Disk 2: 010110
- Disk 3: 110100
- Disk 4: 011101

What were the contents of Disk 5? Explain how you got your answer.

Please answer in THREE SENTENCES OR LESS. Longer explanations may get no credit

```json
{
  "problem_id": "3e",
  "points": 3,
  "type": "Freeform",
  "tags": ["operating-systems", "storage", "raid"],
  "reference_materials": ["rust_reference.md"],
  "answer": "The contents of disk 5 are 011101. This can be calculated by taking the bitwise XOR of all the data on disks 1, 2, 3, and 4.",
  "llm_judge_instructions": "Award full points for a fully correct explanation. award partial credit for partially correct explanations"
}
```

---

## Question 4a [4 points]

Suppose we have a hard drive with the following specifications:

- An average seek time of 10 ms.
- A rotational speed of 6000 revolutions per minute.
- A controller that can transfer data at a rate of 40 MB/s.

What is the expected throughput of the hard drive when reading a 4 KB sector from a random location on disk? You may ignore queueing delay. Please leave your answer as a fraction (KB/ms) in simplest form.

We may give partial credit if you show your work.

```json
{
  "problem_id": "4a",
  "points": 4,
  "type": "Freeform",
  "tags": ["operating-systems", "storage", "hdd"],
  "reference_materials": ["rust_reference.md"],
  "answer": "The total time is the seek time plus the rotation time plus the transfer time. Since the disk runs at 6000 RPM, a single revolution takes 10ms. So the average rotation time is 5ms. Transferring 4KB at a rate of 40 MB/s takes 0.1ms. Thus, the total time is 10ms + 5ms + 0.1ms = 15.1ms. So the expected throughput is 4 KB/15.1 ms."
}
```

---

## Question 4b [4 points]

Anakin Skywalker has a computer that:

- Has a single-level page table.
- Has a TLB.
- Has a single cache.

Furthermore, suppose:

- Each main memory access takes 100ns.
- Each TLB access takes 10ns.
- The cache has a 30ns lookup time.
- Cache and TLB lookups do not overlap.
- Both the TLB and the cache have a 90% hit rate.

What is the expected time to read from a location in memory? Please leave your answer in ns. We may
give partial credit if you show your work.

```json
{
  "problem_id": "4b",
  "points": 4,
  "type": "Freeform",
  "tags": ["operating-systems", "virtual-memory", "caching", "tlb"],
  "reference_materials": ["rust_reference.md"],
  "answer": "The average cache lookup time is C = 0.9 * 30ns + 0.1(30ns + 100ns) = 40ns. The AMAT is 0.9 * (10ns + C) + 0.1 * (10ns + 2C) = 54ns"
}
```

---

## Question 4c [4 points]

Suppose we have resources A, B, C and threads T1, T2, T3, T4. The total number of each resource as well as the current/max allocations for each thread are as follows:

Total Allocation: A=5, B=6, C=7

Current Allocation:
| Thread | A | B | C |
|--------|---|---|---|
| T1     | 1 | 2 | 0 |
| T2     | 0 | 1 | 1 |
| T3     | 2 | 0 | 3 |
| T4     | 1 | 1 | 1 |

Max Allocation:
| Thread | A | B | C |
|--------|---|---|---|
| T1     | 2 | 4 | 3 |
| T2     | 3 | 2 | 5 |
| T3     | 3 | 4 | 3 |
| T4     | 2 | 3 | 3 |

Is this system in a safe state? If so, provide a non-blocking ordering of threads. If not, explain why.

```json
{
  "problem_id": "4c",
  "points": 4,
  "type": "Freeform",
  "tags": ["operating-systems", "concurrency", "deadlock", "bankers-algorithm"],
  "reference_materials": ["rust_reference.md"],
  "answer": "This is a safe state. There are 2 possible orderings: T4, T1, T2, T3, or T4, T1, T3, T2"
}
```

---

## Question 5 [10 points]

Consider a multi-level memory management scheme with the following format for virtual addresses:

```
+------------------------------------------------+
| Virtual Page #1 | Virtual Page #2 | Offset     |
| (10 bits)       | (10 bits)       | (12 bits)  |
+------------------------------------------------+
```

Virtual addresses are translated into physical addresses of the following form:

```
+-------------------------------+
| Physical Page # | Offset      |
| (20 bits)       | (12 bits)   |
+-------------------------------+
```

Page table entries (PTE) are 32 bits in the following form:

```
+-----------------------------------------------------------------+
| Physical Page # | OS      | 0 | 0 | D | A | N | WT | U | W | V |
| (20 bits)       | (3 bits)|   |   |   |   |   |    |   |   |   |
+-----------------------------------------------------------------+
```

where D, A, N, WT, U, W, V are status bits. In this problem, V = 1 means the PTE is valid. Otherwise V = 0. You do NOT need to worry about any of the other status bits.

Translating virtual addresses to physical addresses typically occurs in hardware. However, Kenobi decides to write a kernel function that takes a 32-bit virtual address and returns the corresponding 32-bit physical address.
Help Kenobi implement his lookup function by filling in the code below. You can ONLY call functions that are provided below.

Hint: << and >> operators may be helpful.

Given the following function signature and setup code:

```c
#include <inttypes.h>
#include <stdbool.h>

/*
* Kernel page fault handler.
*/
void page_fault_handler(uint32_t vaddr) {
  ...
}

/*
* Gets the 32-bit word at the 32-bit physical address PADDR.
*/
uint32_t get_word(uint32_t paddr) {
  ...
}

/*
* ZEROS OUT bits of INPUT from start index to end index, including START but not END.
* Index 0 is the least significant bit. Index 31 is the most significant bit.
* 0 <= start < end <= 32 must be true or zero will panic.
*/
uint32_t zero(uint32_t input, int start, int end) {
  ...
}

/*
* Page address translation in the kernel.
* VADDR is the 32-bit virtual addr to be translated.
* PT is the 32-bit physical addr of the base page table. It is page-aligned.
* This function returns the 32-bit physical addr corresponding to VADDR.
* If VADDR is not mapped, call page_fault_handler(vaddr) and return 0 immediately.
* (In other words, if lookup returns 0, then either VADDR was not mapped
* or VADDR maps to 0x00000000.)
*/
uint32_t lookup(uint32_t vaddr, uint32_t pt) {
    uint32_t vpn[2];
    uint32_t ptentry;
    bool valid;

    _________________[A (x3)]___________________

    for (int i = 0; i < 2; i++) {
        ________________[B (x8)]___________________
    }

    ________________[C (x1)]_________________
}
```

Fill in sections [A], [B], and [C]:

- [A] (max 3 lines)
- [B] (max 8 lines)
- [C] (max 1 line)

```json
{
  "problem_id": "5",
  "points": 10,
  "type": "Freeform",
  "tags": ["operating-systems", "virtual-memory", "page-tables"],
  "reference_materials": ["rust_reference.md"],
  "answer": "[A]:\nvpn[0] = vaddr >> 22;\nvpn[1] = zero(vaddr >> 12, 10, 32);\n\n[B]:\nptentry = get_word(pt + 4*vpn[i]);\nif ((ptentry & 1) == 0) {\n    page_fault_handler(vaddr);\n    return 0;\n}\npt = zero(ptentry, 0, 12);\n\n[C]:\nreturn pt + zero(vaddr, 12, 32);",
  "llm_judge_instructions": "Grade each section separately and sum the points"
}
```

---

## Question 6 [21 points]

In this problem, we will implement a reliable key-value store.

The key-value store will support two operations:

- PUT(list(k, v)): Stores an ordered list of key-value pairs into the key-value store in a single transaction. Duplicate keys may be present.
- GET(k): Gets the value corresponding to a single key.

PUT operations act like transactions; they must be atomic. That is, suppose a client executes this PUT:

x = 5
y = 7
x = 2

No clients should see the temporary assignment of x to 5. A PUT operation is considered committed if and when the KvStore::put method returns Ok(()).

The key-value store must be reliable: data from committed PUT operations must be retained even if the key-value store crashes and restarts. Data written to disk (eg. the log) will be retained between crashes and is loaded at startup.

To achieve reliability, we will use journaling. We will maintain a durable log containing a record of operations applied to the key-value store. A log entry is represented by the LogEntry struct.

You are given an implementation of a log for a key-value store; its API is shown in the code below. You are also given some helper functions for interacting with the filesystem, but you should NOT need to use them in the sections of code you write.

For performance reasons, there are some restrictions on when and how you can acquire locks:

- You may never acquire the log lock at the same time as the data lock, except in checkpoint.
- You may never acquire the log lock in write mode, except in checkpoint.
- Your implementation must not be prone to deadlock.

Remember that calling drop on a lock guard causes the lock to be released immediately.

Fill in the implementations of get and checkpoint.

- get returns the value corresponding to the given key as of the last committed transaction. We consider the last transaction to be the one with the highest transaction ID.
- checkpoint safely deletes all log entries corresponding to committed transactions. A crash during checkpoint must not result in data loss. Log entries for uncommitted transactions should be kept in the log.

Your key-value store should provide correct results regardless of if or when a crash occurs. Functions marked atomic in the skeleton code can be assumed to complete successfully, or not complete at all. In other words, a crash will not cause an atomic operation to only partially complete. (Non-atomic operations, on the other hand, may be partially complete if a crash occurs.)

```rust
//! A durable key-value store that uses a write-ahead log.
use anyhow::Result;
use std::{
  collections::HashMap,
  sync::Arc,
};
use tokio::sync::RwLock;
type TransactionId = u64;

struct KvStore {
  log: Arc<RwLock<Log>>,
  data: Arc<RwLock<HashMap<String, String>>>,
}
struct Log {
  // Hidden
}
struct LogEntry {
  tx_id: TransactionId,
  record: LogRecord,
}
#[derive(Eq, PartialEq)]
enum LogRecord {
  BeginTx,
  Put(String, String),
  CommitTx,
}
impl Log {
  /// Load a log from `path`, or create a new one if `path` does not exist or is corrupted.
  /// NOT atomic.
  async fn new(path: &str) -> Result<Self> { ... }
  /// Begins a transaction, returning the transaction ID. ATOMIC.
  async fn begin(&self) -> Result<TransactionId> { ... }
  /// Records a SINGLE key-value pair. NOT atomic.
  async fn put(&self, tx_id: TransactionId, k: &str, v: &str) -> Result<()> { ... }
  /// Marks the given transaction as committed. ATOMIC.
  async fn commit(&self, tx_id: TransactionId) -> Result<()> { ... }
  /// Returns a list of all log entries.
  async fn entries(&self) -> Result<Vec<LogEntry>> { ... }
  /// Returns true if the given transaction was committed.
  async fn committed(&self, tx_id: TransactionId) -> bool { ... }
  /// Deletes all log entries, and writes the given entries in their place. NOT atomic.
  /// If a crash occurs during this function, the log will become corrupted.
  /// Subsequent calls to `Log::new` will provide an empty log.
  async fn set(&mut self, entries: Vec<LogEntry>) -> Result<()> { ... }
}
/// Saves `data` at `path`. NOT atomic.
async fn persist(path: &str, data: &HashMap<String, String>) -> Result<()> { ... }
/// Loads a saved HashMap from `path`. NOT atomic.
async fn load(path: &str) -> Result<HashMap<String, String>> { ... }
/// Renames file `src` to `dst`. ATOMIC.
async fn rename(src: &str, dst: &str) -> Result<()> { ... }
/// Deletes a file saved at `path`. ATOMIC.
async fn remove(path: &str) -> Result<()> { ... }

const KV_LOG: &str = "kv.log";
const KV_DATA: &str = "kv.dat";
const TMP_DATA: &str = "tmp.dat";

impl KvStore {
  async fn init() -> Result<Self> {
    Ok(Self {
      log: Arc::new(RwLock::new(Log::new(KV_LOG).await?)),
      data: Arc::new(RwLock::new(HashMap::new())),
    })
  }
  async fn put(&self, entries: Vec<(String, String)>) -> Result<()> {
    let log = self.log.read().await;
    let tx_id = log.begin().await?;
    for (k, v) in entries {
      log.put(tx_id, &k, &v).await?;
    }
    log.commit(tx_id).await?;
    Ok(())
  }
  async fn get(&self, key: String) -> Result<Option<String>> {
    let log = self.log.read().await;
    let entries = log.entries().await?;
    ________________[A (x25)]__________________
  }
  async fn checkpoint(&self) -> Result<()> {
    let mut data = self.data.write().await;
    let mut log = self.log.write().await;
    let entries = log.entries().await?;
    let mut keep = Vec::new();
    ________________[B (x20)]__________________
    persist(TMP_DATA, &data).await?;
    rename(TMP_DATA, KV_DATA).await?;
    let _ = remove(TMP_DATA).await;
    log.set(keep).await?;
    Ok(())
  }
}
```

Note: Minor Rust syntax errors are acceptable.

Fill in:
- [A] (max 25 lines): Implement get
- [B] (max 20 lines): Implement checkpoint

```json
{
  "problem_id": "6",
  "points": 21,
  "type": "Freeform",
  "tags": ["rust", "distributed-systems", "journaling", "transactions"],
  "reference_materials": ["rust_reference.md"],
  "answer": "# A\n```rust\nlet mut last_tx = 0;\nlet mut value = None;\nfor record in records {\n  if let LogEntry::Put(k, v) = record.entry {\n    if k == key && log.committed(record.tx_id).await {\n      if record.tx_id >= last_tx {\n        last_tx = record.tx_id;\n        value = Some(v);\n      }\n    }\n  }\n}\nif value.is_some() {\n  return Ok(value);\n}\ndrop(log);\nlet data = self.data.read().await;\nOk(data.get(&key).cloned())\n```\nWe first check the log to see if there is a committed transaction that modified the key we are looking for. We want GET to return the value saved by the last (ie. highest ID) transaction, so we create a temporary variable called last_tx to store the highest transaction ID we've seen so far that modifies the given key.\n\nFor each log record, we check if it is a PUT record, modifies the right key, is committed, and has a transaction ID greater than or equal to last_tx.\n\nIf no value is found in the log, we check the data HashMap\n# B\n```rust\nlet mut last_tx = HashMap::new();\nfor record in records {\n  if log.committed(record.tx_id).await {\n    if let LogEntry::Put(k, v) = record.entry {\n      if record.tx_id >= last_tx.get(&k).copied().unwrap_or(0) {\n        last_tx.insert(k.clone(), record.tx_id);\n        data.insert(k, v);\n      }\n    }\n  } else {\n    keep.push(record);\n  }\n}\n```\nWe want to clear all log entries from committed transactions. So we loop through the log entries. If an entry is not committed, we save it in the keep list. For committed entries, we update the data HashMap only if the transaction is committed, the log entry is a PUT entry, and no later transaction set a value for the key in the log entry.\n\nTo see why the last condition is necessary, consider the following log (which is not prevented by the given implementation of put):\n\n- 15: BEGIN TX\n- 16: BEGIN TX\n- 16: PUT x = 2\n- 15: PUT x = 1\n- COMMIT 16\n- COMMIT 15\n\nWe want to see x=2, since this is the value of x from the transaction with the highest ID (16). However, the PUT record for transaction 15 appears later in the log than the PUT record for transaction 16",
  "llm_judge_instructions": "[A] get (12 pts): returns value from highest committed tx_id for key, falls back to data HashMap. [B] checkpoint (9 pts): uncommitted entries go to keep, committed Put entries update data HashMap respecting highest tx_id per key."
}
```