# 6.1810 Operating System Engineering - Fall 2024 Final Exam

```json
{
  "exam_id": "6_1810_operating_system_engineering_fall_2024_final",
  "test_paper_name": "6.1810 Operating System Engineering: Fall 2024 Final Exam",
  "course": "6.1810",
  "institution": "MIT",
  "year": 2024,
  "score_total": 70,
  "score_max": 67.5,
  "score_avg": 49.88,
  "score_median": 49,
  "score_standard_deviation": 11.07,
  "num_questions": 14
}
```

---

## Question 1 [5 points]

Ben makes a fresh fs.img, boots xv6, and runs the following commands:

```
$ mkdir a
$ mkdir a/b
```

How many inodes will xv6 allocate while executing these two commands?

A. 0

B. 1

C. 2

D. 3

Your answer should be one of: A, B, C, D only (no extra text).

```json
{
  "problem_id": "1",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["file-systems", "xv6", "inodes"],
  "answer": "C",
  "comments": "C. A directory is implemented using an inode, and one inode is created for directory a and one is created for directory b"
}
```

---

## Question 2 [5 points]

Alyssa adds the statement:

```
printf("write: %d\n", b->blockno);
```

to xv6's log write in log.c. She then makes a fresh fs.img, boots xv6, and runs the following
command:

```
$ mkdir a
write: 33
write: 33
write: 45
write: 770
write: 770
write: 33
write: 770
write: 33
write: 46
write: 32
write: 32
```

What does block 770 contain?

A. directory entries

B. inodes

C. file data

D. a bitmap

Your answer should be one of: A, B, C, D only (no extra text).

```json
{
  "problem_id": "2",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["file-systems", "xv6", "logging"],
  "answer": "A",
  "comments": "A. Block 770 is a data block and data blocks of directories contain directory entries."
}
```

---

## Question 3 [5 points]

Ben makes a fresh fs.img, boots xv6, and runs a program that makes the following system call:

```
symlink("b", "b");
```

From the shell he then runs:

```
$ cat b
```

What will the result of the cat be?

A. 'b'

B. an error because 'b' doesn't exist

C. an error because 'b' points to itself

D. nothing because xv6 will panic

Your answer should be one of: A, B, C, D only (no extra text).

```json
{
  "problem_id": "3",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["file-systems", "xv6", "symlinks"],
  "answer": "C",
  "comments": "C. When the kernel resolves the symlink 'b' in open, it will find the symlink 'b'. The fs lab requires your solution detects this cycle and return an error."
}
```

---

## Question 4 [5 points]

Recall the Linux EXT3 journaling file system from Journaling the Linux ext2fs Filesystem and Lecture 15. The paper's 'ext2fs' is the same as EXT3.

Suppose that the current compound transaction has just closed (see step 1 on the paper's page 6) and is starting to commit.

How long must new file-system system calls wait until they can start executing?

A. New system calls can start immediately.

B. New system calls must wait until all system calls in the just-closed transaction have completed.

C. New system calls must wait until the just-closed transaction has started to write journal blocks to the journal.

D. New system calls cannot start until the just-closed transaction has finished committing to the journal.

E. New system calls cannot start until all updated buffers from the just-closed transaction have been synced to their homes on disk.

Your answer should be one of: A, B, C, D, E only (no extra text).

```json
{
  "problem_id": "4",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["file-systems", "journaling", "ext3"],
  "answer": "B",
  "comments": "B. The delay serves to prevent partial modifications made by system calls in the next transaction from being seen by system calls that are finishing in the first transaction."
}
```

---

## Question 5 [5 points]

Hatshepsut is building an application on Linux that creates a set of directories, and she would like the set of creations to be atomic with respect to crashes. She's using the EXT3 file system. She experiments with this application code:

```
int main() {
    mkdir("/aaa", 0777);
    mkdir("/zzz", 0777);
    exit(0);
}
```

(The 0777 is needed for Linux, though not for xv6; it does not affect this question.)

Hatshepsut runs this program. Both calls to mkdir() return success. Hatshepsut causes her computer to
crash just after the program exits. Then she re-starts the computer, which runs the EXT3 recovery program.

What could Hatshepsut see after recovery? (Choose all that apply.)
A. She might see neither /aaa nor /zzz.

B. She might see /aaa but not /zzz.

C. She might see /zzz but not /aaa.

D. She might see both /zzz and /aaa.

E. None of the above.

Your answer should be a comma-separated list of letters only (no extra text). For example: "B, C"

```json
{
  "problem_id": "5",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["file-systems", "journaling", "ext3", "atomicity"],
  "answer": "A, B, D",
  "comments": "A, B, and D. A can occur if the system crashed before the transaction(s) reflecting the mkdirs finished committing. B can occur if the two mkdirs are in different transactions, and only the first manages to finish committing. C cannot occur because system calls are placed in transactions in order, and the transactions are also replayed in order during recovery"
}
```

---

## Question 6 [5 points]

Below is a code fragment illustrating how a user program can implement a large table of square roots with Linux VM primitives while using little physical memory. (The full code presented in reference materials)

```
1 static size_t page_size;
2 #define MAX_SQRTS 3
4 static double *sqrts;
5
6 // The page handler catching page faults
7 static void
8 handle_sigsegv(int sig, siginfo_t *si, void *ctx)
9 {
10 uintptr_t fault_addr = (uintptr_t)si->si_addr;
11 double *page_base = (double *)align_down(fault_addr, page_size);
12 static double *last_page_base = NULL;
13
14 if (last_page_base && munmap(last_page_base, page_size) == -1) {
15 fprintf(stderr, "Couldn't munmap(); %s\n", strerror(errno));
16 exit(EXIT_FAILURE);
17 }
18
19 if (mmap(page_base, page_size, PROT_READ | PROT_WRITE,
20 MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0) == MAP_FAILED) {
21 fprintf(stderr, "Couldn't mmap(); %s\n", strerror(errno));
22 exit(EXIT_FAILURE);
23 }
24
25 calculate_sqrts(page_base, page_base - sqrts, page_size / sizeof(double));
26 last_page_base = page_base;
27 }
28
29 // Simplified version of the test function
30 static void
31 test_sqrt_region(void)
32 {
33 int i, pos;
34 double s;
35
36 // Find a sufficiently-large unused range of virtual addresses, and
37 // sets sqrts to the start.
38 setup_sqrt_region();
39
40 // look up some numbers in the sqrt table
41 for (i = 0; i < 8192; i++) {
42 s = sqrts[i];
43 printf("sqrt %f", s);
44 }
45 }
```

Assume size of double is 8 bytes and page size is 4096 bytes.

Assume the sqrts table occupies 0 pages of physical memory after the return from setup sqrt region. How many pages of physical memory does the sqrts table occupy when test sqrt region returns? (You can ignore physical memory pages used for the page table itself.)

A. 0

B. 1

C. 1000

D. ((1 ≪ 27) \* 8) / 4096

Your answer should be one of: A, B, C, D only (no extra text).

```json
{
  "problem_id": "6",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["virtual-memory", "linux", "page-faults"],
  "reference_materials": ["mmap.md"],
  "answer": "B",
  "comments": "B. The page fault handler uses only 1 page. If it maps a new page, it unmaps the old page."
}
```

---

## Question 7 [5 points]

Below is a code fragment illustrating how a user program can implement a large table of square roots with Linux VM primitives while using little physical memory. (The full code presented in reference materials)

```
1 static size_t page_size;
2 #define MAX_SQRTS 3
4 static double *sqrts;
5
6 // The page handler catching page faults
7 static void
8 handle_sigsegv(int sig, siginfo_t *si, void *ctx)
9 {
10 uintptr_t fault_addr = (uintptr_t)si->si_addr;
11 double *page_base = (double *)align_down(fault_addr, page_size);
12 static double *last_page_base = NULL;
13
14 if (last_page_base && munmap(last_page_base, page_size) == -1) {
15 fprintf(stderr, "Couldn't munmap(); %s\n", strerror(errno));
16 exit(EXIT_FAILURE);
17 }
18
19 if (mmap(page_base, page_size, PROT_READ | PROT_WRITE,
20 MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0) == MAP_FAILED) {
21 fprintf(stderr, "Couldn't mmap(); %s\n", strerror(errno));
22 exit(EXIT_FAILURE);
23 }
24
25 calculate_sqrts(page_base, page_base - sqrts, page_size / sizeof(double));
26 last_page_base = page_base;
27 }
28
29 // Simplified version of the test function
30 static void
31 test_sqrt_region(void)
32 {
33 int i, pos;
34 double s;
35
36 // Find a sufficiently-large unused range of virtual addresses, and
37 // sets sqrts to the start.
38 setup_sqrt_region();
39
40 // look up some numbers in the sqrt table
41 for (i = 0; i < 8192; i++) {
42 s = sqrts[i];
43 printf("sqrt %f", s);
44 }
45 }
```

Assume size of double is 8 bytes and page size is 4096 bytes.

How many total page faults will the repeated execution of line 42 cause?

A. 0

B. 1

C. 2

D. 16

E. 8192

Your answer should be one of: A, B, C, D, E only (no extra text).

```json
{
  "problem_id": "7",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["virtual-memory", "linux", "page-faults"],
  "reference_materials": ["mmap.md"],
  "answer": "D",
  "comments": "D. The loop goes through the first 8192 entries in the sqrts table. A double is 8 bytes and 512 fit on a single page of 4096 bytes (4096/8 = 512). Thus, the total number of virtual pages referenced in the loop is 8192/512 = 16. The page fault handler will be invoked once for each of the 16 pages."
}
```

---

## Question 8 [5 points]

Consider The Performance of µ-Kernel-Based Systems, by Hartig et al.,
Suppose that an sh Linux process running under L4Linux performs a fork().

Which of the following are true? (Choose all that apply.)

A. The L4 kernel's fork() system call copies the sh process's memory.

B. When the Linux kernel server task has finished executing the system call implementation, it executes the x86 equivalent of RISC-V sret to return to the sh process.

C. When the Linux kernel server task returns to the newly created child process, the Linux kernel changes the hardware page table register (equivalent of RISC-V satp) to point to the child process's page table.

D. Copy-on-write fork() is not possble for L4Linux because the CPU delivers page faults to the L4 kernel, not to the Linux kernel task.

E. None of the above.

Your answer should be a comma-separated list of letters only (no extra text). For example: "B, C"

```json
{
  "problem_id": "8",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["microkernels", "l4linux", "fork"],
  "answer": "E",
  "comments": "E. Not A: fork is a Linux system call, implemented by the Linux kernel server, not by the L4 kernel. Not B: Linux processes communicate with the Linux server via IPC messages, not by system call traps. Not C: The Linux kernel server is not privileged, and cannot modify the page table register; only the L4 kernel can do this. Not D: the L4 kernel forwards page faults to the Linux kernel server."
}
```

---

## Question 9 [5 points]

Consider RedLeaf: Isolation and Communication in a Safe Operating System by Narayanan et al.

Which of the following are true statements about RedLeaf's design? (Choose all that apply.)

A. Because the RedLeaf microkernel and domains run in a single address space, a domain can read any kernel memory by dereferencing a Rust pointer.

B. User programs can avoid data copies by passing pointers to their private memory to other user programs.

C. Two domains can have a Rust pointer to an object on the shared heap at the same time.

D. The rv6 file system can be modified to support memory-mapped files using the same ideas as in the mmap lab without modifying the RedLeaf microkernel.

E. A divide-by-zero error in the network domain won't crash the rv6 file system.

F. None of the above.

Your answer should be a comma-separated list of letters only (no extra text). For example: "B, C"

```json
{
  "problem_id": "9",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["redleaf"],
  "answer": "C, E",
  "comments": "C and E. A is false because RedLeaf uses language techniques that disallow domains to dereferences arbitrary addresses. B is false, because RedLeaf explicitly disallows this; only pointers in the shared heap can be passed to other domains. C is true, because RedLeaf follows the Rust borrow rules, which allow two domains to have an immutable reference to the same object. D is false, because RedLeaf doesn't use page tables but relies on language techniques for isolation; the mmap lab requires the use of page tables. E is true, because RedLeaf is designed to catch errors like these and clean up a domain that experience such an error."
}
```

---

## Question 10 [5 points]

Consider Eliminating Receive Livelock in an Interrupt-driven Kernel, by Mogul et al., and Lecture 20.

Ben implements the paper's polling design (Section 6.4), in which the NIC interrupt handler just wakes up the polling thread. However, Ben's implementation leaves NIC interrupts enabled (in contrast to Section 6.4, which specifies that they be disabled until the polling thread is done). Ben's computer has just one CPU (i.e. just a single core).

What will Ben observe as the rate of packet arrivals increases? (Choose the best answer.)

A. He won't see livelock, because the interrupt handler doesn't process the packets; only the polling thread handles the packets.

B. He won't see livelock, because the polling design eliminates the IP input queue, which was the point at which packets were discarded in the old design.

C. He will see livelock, because at high enough arrival rates the CPU will spend all its time in the polling thread.

D. He will see livelock, because at high enough arrival rates the CPU will spend all its time in the interrupt handler.

E. He will see livelock, because the polling thread can only process packets at some finite rate, and the input rate could be higher than that.

Your answer should be one of: A, B, C, D, E only (no extra text).

```json
{
  "problem_id": "10",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["operating-systems", "networking"],
  "answer": "D"
}
```

---

## Question 11 [5 points]

Zoe's xv6 computer has a UART that has no limit on how fast it can transmit bytes. The UART interrupts once per byte transmitted, to indicate that it has finished transmitting the byte. Zoe has a program whose standard output (file descriptor 1) is connected to the xv6 console, which uses the UART; the program sends bytes as fast as it can:

```
while(1){
    char c = 'x';
    write(1, &c, 1);
}
```

Zoe's computer has just one CPU (i.e. just a single core).

Could this program cause interrupt livelock due to the CPU spending all its time in the UART interrupt handler, and thus no time executing Zoe's program? Explain briefly.

Your answer should be either "Yes" or "No" followed by a brief explanation (no more than 2 sentences).

```json
{
  "problem_id": "11",
  "points": 5,
  "type": "Freeform",
  "tags": ["operating-systems", "networking", "interrupts"],
  "answer": "No. The UART interrupts just once for each call to write(). There can't be more than a brief period of time in which UART interrupts prevent Zoe's program from running, because the UART driver will soon run out of bytes to transmit.",
  "llm_judge_instructions": "Evaluate the answer for correctness and completeness. Assign full points for a correct and complete explanation, partial points for a partially correct explanation, and zero points for an incorrect explanation."
}
```

---

## Question 12 [5 points]

Below is Listing 2 of the paper Meltdown: reading kernel memory from user space by Lipp et al., written in a C-like notation instead of x86 assembly.

```
1 char buf[8192]
2
3 // The flush part of Flush+Reload
4 cflush buf[0]
5 cflush buf[4096]
6
7 // The core attack from listing 2
8 r1 = 0x79cbcc0 // a kernel virtual address
9 r2 = _r1
10 r2 = r2 & 1
11 r2 = r2 _ 4096
12 r3 = buf[r2]
```

Which of the following are true statements? (Choose all that apply.)

A. In Linux as described in the paper, page tables of user programs map all of kernel memory.

B. Loading the value at kernel address 0x79cbcc0 on line 9 will lead to an exception.

C. If the attack succeeds, then buf[0] will be in the L1 cache if the low bit of the value at address 0x79cbcc0 is a 0.

D. One reason why one run of Meltdown might not succeed is because buf[0] maybe evicted from the L1 cache before the attack can measure its presence using Reload.

E. The Meltdown attack on xv6 wouldn't be able to dump all of xv6 kernel memory because like KAISER the xv6 kernel and user processes have separate page tables.

F. None of the above.

Your answer should be a comma-separated list of letters only (no extra text). For example: "B, C"

```json
{
  "problem_id": "12",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["meltdown"],
  "answer": "A, B, C, D, E",
  "comments": "A, B, C, D, and E. B is true because eventually the CPU will generate an exception, perhaps after speculating on a few instructions. E is true, because xv6 has separate kernel and user page tables, and the user page tables don't map all of kernel memory."
}
```

---

## Question 13 [5 points]

Ben has a Linux kernel that uses RCU as described in RCU Usage In the Linux Kernel: One Decade Later, by McKenney et al. He modifies udp sendmsg() in the paper's Figure 6, adding a call to new function() on line 8, so that the code now reads:

```
1 void udp*sendmsg(sock_t *sock, msg_t *msg)
2 {
3 ip_options_t \*opts;
4 char packet[];
5 copy_msg(packet, msg);
6 rcu_read_lock();
7 opts = rcu_dereference(sock->opts);
8 new_function(); // \*\** Ben adds this line. \_\**
9 if (opts != NULL)
10 copy_opts(packet, opts);
11 rcu_read_unlock();
12 queue_packet(packet);
13 }
14 void setsockopt(sock_t *sock, int opt, void *arg)
15 {
16 if (opt == IP_OPTIONS) {
17 ip_options_t *old = sock->opts;
18 ip_options_t \*new = arg;
19 rcu_assign_pointer(&sock->opts, new);
20 if (old != NULL)
21 call_rcu(kfree, old);
22 return;
23 }
24 }
```

This code is otherwise identical to the paper's Figure 6.
new function() performs a context switch (i.e., it calls the Linux equivalent of xv6's sleep() or yield()).

Ben has made a mistake. Explain a scenario in which something goes wrong with the Figure 6 code as a result of Ben's change

```json
{
  "problem_id": "13",
  "points": 5,
  "type": "Freeform",
  "tags": ["operating-systems", "concurrency", "rcu"],
  "answer": "Use-after-free. If new_function() causes a context switch, then call_rcu() could call kfree(old), and that memory could be re-allocated for something else and overwritten. But that's the same memory that opts points to on line 10, which would therefore copy the wrong data.",
  "llm_judge_instructions": "Evaluate the answer for correctness and completeness. Assign full points for a correct and complete explanation, partial points for a partially correct explanation, and zero points for an incorrect explanation."
}
```

---

## Question 14 [5 points]

Ben has a Linux kernel that uses RCU as described in RCU Usage In the Linux Kernel: One Decade Later, by McKenney et al. He modifies udp sendmsg() in the paper's Figure 6, adding a call to new function() on line 8, so that the code now reads:

```
1 void udp*sendmsg(sock_t *sock, msg_t *msg)
2 {
3 ip_options_t \*opts;
4 char packet[];
5 copy_msg(packet, msg);
6 rcu_read_lock();
7 opts = rcu_dereference(sock->opts);
8 new_function(); // \*\** Ben adds this line. \_\**
9 if (opts != NULL)
10 copy_opts(packet, opts);
11 rcu_read_unlock();
12 queue_packet(packet);
13 }
14 void setsockopt(sock_t *sock, int opt, void *arg)
15 {
16 if (opt == IP_OPTIONS) {
17 ip_options_t *old = sock->opts;
18 ip_options_t \*new = arg;
19 rcu_assign_pointer(&sock->opts, new);
20 if (old != NULL)
21 call_rcu(kfree, old);
22 return;
23 }
24 }
```

This code is otherwise identical to the paper's Figure 6.
new function() performs a context switch (i.e., it calls the Linux equivalent of xv6's sleep() or yield()).

Now Ben is working on the code in the RCU paper's Figure 7. He reasons that the kfree(local table) in retract table() really belongs inside the critical section, so that the entire sequence is atomic. He moves that line, resulting in this code:

```
...;
spin_lock(&table_lock);
local_table = table;
rcu_assign_pointer(&table, NULL);
kfree(local_table); // *** Ben moved this line. ***
spin_unlock(&table_lock);
...;
```

What problem is Ben's change likely to cause? (Choose the best answer.)

A. Ben's change could cause a deadlock.

B. Ben's change could allow a context switch to occur just before the kfree() call, which would be illegal.

C. Ben's change could cause invoke syscall() to dereference a pointer to freed memory.

D. Ben's change could cause retract table() to dereference a pointer to freed memory.

Your answer should be one of: A, B, C, D only (no extra text).

```json
{
  "problem_id": "14",
  "points": 5,
  "type": "ExactMatch",
  "tags": ["operating-systems", "concurrency", "rcu"],
  "answer": "C",
  "comments": "C. Ben's modified retract table() frees local_table before the call to synchronize_rcu(). An execution of invoke_syscall() might be active at the same time on another CPU, and might read the old value of local_table just after it has been freed and re-used for something else."
}
```
