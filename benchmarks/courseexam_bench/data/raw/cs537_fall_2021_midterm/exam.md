# CS 537 Fall 2021 Midterm

```json
{
  "exam_id": "cs537_fall_2021_midterm",
  "test_paper_name": "CS 537 Fall 2021 Midterm",
  "course": "Operating Systems",
  "institution": "University of Wisconsin-Madison",
  "year": 2021,
  "score_total": 32,
  "num_questions": 32
}
```

---

## Question 1 [5 point(s)]

BeOS keeps track of a small amount of information about each running process in a data structure called the “process list”. However, to keep the amount of information in the process list small, Binus reduced the number of states a process could be in. Specifically, in BeOS, there are only two states a process can be in: RUNNING and BLOCKED. What process state found in most OSes was removed from BeOS?

```json
{
  "problem_id": "1",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["be-os"],
  "choices": ["STOPPED", "READY", "ACTIVE", "WAITING", "LOCKED"],
  "answer": "B"
}
```

---

## Question 2 [3 point(s)]

To  keep  scheduling  simple  in  BeOS,  Binus  chose  the FIFO  policy  (first  in,  first  out)  to  decide  which  process  to  run.  Which one of the following statements about FIFO scheduling is true?

```json
{
  "problem_id": "2",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["fifo-scheduling"],
  "choices": ["It reduces average turnaround time","It reduces average response time","It suffers from the “convoy” problem","It is a preemptive scheduling policy","It is different from the FCFS policy"],
  "answer": "C"
}
```

---

## Question 3 [4 point(s)]

Assuming  the  BeOS  FIFO  scheduling  approach,  calculate  the turnaround  time  for  job  B,  assuming  the  following: job A arrives at time T=0, and needs to perform 10 seconds of compute; job B arrives at time  T=5,  and  needs  to  perform  20  seconds  of  compute;  job  C  arrives  at  time  T=10,  and  needs  to  perform 5 seconds of compute. The jobs perform no I/O.

```json
{
  "problem_id": "3",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["cpu-scheduling"],
  "choices": ["10","20","30","25","None of the above"],
  "answer": "D"
}
```

---

## Question 4 [4 point(s)]

For simplicity, BeOS originally used a “base and bounds” approach to virtual memory. Which one of the following is true about this approach?

```json
{
  "problem_id": "4",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["virtual-memory"],
  "choices": ["It translates addresses more slowly than most other approaches","It prevents internal fragmentation","It enables sharing of code between processes","It provides protection between processes","None of the above (all are false)"],
  "answer": "D"
}
```

---

## Question 5 [3 point(s)]

Assume the following for the original version of BeOS: a 64-byte virtual address space, a system with 512 bytes of physical memory, a base register set to 10, and a bounds register set to 20. A process in BeOS  wishes  to  access  the  following  virtual  memory  addresses:  15,  6,  30,  21,  50.  How  many  of  these accesses are valid (legal) and thus will not trigger a fault?

```json
{
  "problem_id": "5",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["memory-management"],
  "choices": ["1","2","3","4","5"],
  "answer": "B"
}
```

---

## Question 6 [3 point(s)]

A  later  version  of  BeOS  was  developed  for  a  newer  machine  and  had  a  much  larger  virtual  address space: 1  KB.  Assuming  it  is  running  on  a  system  with  16  KB  of  physical  memory,  what  is  the  largest  virtual  address  a BeOS process can generate?

```json
{
  "problem_id": "6",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["memory-management"],
  "choices": ["1000","1023","1024","It depends on the base register","It depends on the bounds register"],
  "answer": "B"
}
```

---

## Question 7 [3 point(s)]

With a base and bounds registers in the MMU, BeOS must take care during process switching. In an
early  version  of  BeOS,  it  was  so  simple  that  the  bounds  register  was  never  updated  upon  a  process
switch, instead using the first value — essentially, a random value — that was placed there. What could
happen as a result? (choose one answer)

```json
{
  "problem_id": "7",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["memory-management"],
  "choices": ["A process could access another process’s memory","A process could fault even though it is accessing what should be valid memory","A process could access physical memory that isn’t assigned to any process","A process could be prevented from accessing valid code","All of the above"],
  "answer": "E"
}
```

---

## Question 8 [3 point(s)]

An  earlier  version  of  BeOS  was  so simple that  it  didn’t  use  the  base  and  bounds registers provided in
hardware.  Instead,  when  a  process  was  loaded  into  memory,  each  of  its  address  references  was
statically rewritten to match its location in physical memory. For example, if the program contained the
instruction  “load  10  into  register  R1”,  and  the  address  space  was  loaded  at  physical  address  100,  the
instruction would be rewritten to “load 110 into register R1”. This approach (choose one answer):

```json
{
  "problem_id": "8",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["memory-management"],
  "choices": ["Provides strong process isolation","Makes programs run slowly","Allows multiple processes to be active in the system","Affects the type of CPU scheduling policy you can implement","Helps realize a sparse virtual address space"],
  "answer": "C"
}
```

---

## Question 9 [3 point(s)]

The  DOS  scheduler  is  based  on  a  random  policy.  Specifically,  every  10  milliseconds  (ms),  a  timer interrupt  goes  off,  and  DOS  picks  a  random  process  to  run.  This  approach  is  most  similar  to  which  following  policy?

```json
{
  "problem_id": "9",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["dos-scheduling"],
  "choices": ["First-in, First-out","Shortest Job First","Round Robin","Shortest Time To Completion First","Rank-order Scheduling"],
  "answer": "C"
}
```

---

## Question 10 [3 point(s)]

With  the  DOS  random  scheduling  policy,  assume  you  have  two  jobs  enter  the  system  at  the  same
time, each of which needs to run for 30 milliseconds. Assume again a 10 ms timer interrupt. What is the
best case average response time for these two jobs?

```json
{
  "problem_id": "10",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["dos-scheduling"],
  "choices": ["0 ms","5 ms","10 ms","15 ms","None of the above"],
  "answer": "B"
}
```

---

## Question 11 [3 point(s)]

With  the  DOS  random  scheduling  policy,  assume  you  have  two  jobs  enter  the  system  at  the  same
time, each of which needs to run for 30 milliseconds. Assume again a 10 ms timer interrupt. What is the
worst case average turnaround time for these two jobs?

```json
{
  "problem_id": "11",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["dos-scheduling"],
  "choices": ["45 ms","50 ms","60 ms","120 ms","None of the above"],
  "answer": "E"
}
```

---

## Question 12 [3 point(s)]

DOS  uses  the  MLFQ  (multi-level  feedback  queue)  scheduler.  However,  it  changes  some  rules.  The
biggest  change:  new  processes  are  added  to  a random  queue  (not  the  topmost  one).  What  is  the
biggest effect this will have? (choose one)

```json
{
  "problem_id": "12",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["dos-scheduling"],
  "choices": ["Sometimes, short-running jobs won’t get serviced quickly, thus decreasing interactivity","Over a long period of time, it will be unfair to long-running jobs","Jobs will generally finish more quickly","Jobs will be able to game the scheduler","None of the above"],
  "answer": "A"
}
```

---

## Question 13 [3 point(s)]

DOS  uses  paging.  Before  talking  about  how  randomness  was  used,  let’s  do  a  simple  question  to
make sure we understand it. In this system, the virtual address space size was 128 bytes (tiny!), and the
page size was just 2 bytes. How many entries were in each page table? (assume a linear array)

```json
{
  "problem_id": "13",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["dos-paging"],
  "choices": ["128","64","32","16","None of the above"],
  "answer": "B"
}
```

---

## Question 14 [3 point(s)]

Now assume the address space size is still 128 bytes, but the page size is 32 bytes. Here is the page
table for a process, where the leftmost bit is the valid bit, and the rightmost 4 bits are the PFN.
  0x8000000c
  0x00000000
  0x00000000
  0x80000006
If 4 bits are needed for the PFN, how big is physical memory?

```json
{
  "problem_id": "14",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["dos-paging"],
  "choices": ["128 bytes","256 bytes","512 bytes","1024 bytes","None of the above"],
  "answer": "C"
}
```

---

## Question 15 [3 point(s)]

Assume  again  that  the  address  space  size  is  128  bytes,  and  the  page  size  is  32  bytes.  Using  the
page table above (Question 14), translate the virtual address 0x64.

```json
{
  "problem_id": "15",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["dos-paging"],
  "choices": ["0x46","0x04","0xc4","0x64","None of the above"],
  "answer": "C"
}
```

---

## Question 16 [3 point(s)]

When allocating a physical page to a process, DOS selects a random free physical page (instead of,
for example, the first free one on a free list). This approach will:

```json
{
  "problem_id": "16",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["dos-memory-management"],
  "choices": ["Make the page table larger","Make physical memory more fragmented (externally)","Slow down address translation","Make heap allocation fail more often","None of the above"],
  "answer": "E"
}
```

---

## Question 17 [3 point(s)]

Minux  uses  kernel  mode,  user  mode,  and  a  new  mode  called  “supervisor”  mode.  When  a  user
program runs in “supervisor” mode, it is still restricted (like user mode), but can do the following: change
the  length  of  the  timer  interrupt  interval,  including  turning  it  off.  Overall,  would  you  say  that  supervisor
mode (choose one):

```json
{
  "problem_id": "17",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["minux"],
  "choices": ["Helps ensure streamlined round-robin scheduling","Ensures more efficient, application-aware timing interrupts","Better integrates scheduling and virtual memory mechanisms","Limits the OS’s ability to retain control of the machine if user code runs in supervisor mode","None of the above"],
  "answer": "D"
}
```

---

## Question 18 [3 point(s)]

Minux employs a (two-level) multi-level page table. Assume a 32-bit virtual address space, and 4 KB
pages. Also assume each page table entry (PTE) is 4 bytes in size. How many PTEs fit onto one page?

```json
{
  "problem_id": "18",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["minux"],
  "choices": ["1","32","1024","4096","None of the above"],
  "answer": "C"
}
```

---

## Question 19 [3 point(s)]

Assuming a two-level multi-level page table (32-bit virtual addresses, 4KB pages, 4-byte PTE size),
what  is  the  minimum  number  of  valid  virtual  pages  in  an  address  space  such  that  the  multi-level  page
table becomes its maximum size?

```json
{
  "problem_id": "19",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["minux"],
  "choices": ["512","1024","2048","4096","None of the above"],
  "answer": "B"
}
```

---

## Question 20 [3 point(s)]

Assuming a two-level multi-level page table (32-bit virtual addresses, 4KB pages, 4-byte PTE size),
what  is  the  minimum  number  of  pages  needed  for  the  multi-level  page  table  (including  the  page
directory) when there are 1025 contiguous valid pages somewhere in the virtual address space?

```json
{
  "problem_id": "20",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["minux"],
  "choices": ["3","4","5","1025","None of the above"],
  "answer": "A"
}
```

---

## Question 21 [3 point(s)]

TLBs  make  hardware  more  complex,  so  Minux  definitely  uses  one.  The  best  description  of  what  a
TLB is as follows (choose one):

```json
{
  "problem_id": "21",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["minux-tlb"],
  "choices": ["A memory to store page table entries","A collection of base/bounds pairs to help segmentation work quickly","An OS component to speed up translation","A hardware feature that ensures fair use of memory","An address-translation cache"],
  "answer": "E"
}
```

---

## Question 22 [3 point(s)]

Assume the TLB, which has just four entries, has the following contents (numbers in the TLB are all
decimal, and entries are all valid):
  VPN 0 -> PFN 1
  VPN 1 -> PFN 100
  VPN 2 -> PFN 101
  VPN 3 -> PFN 102
Assume this system has a 14-bit virtual address, and 4-KB pages. What virtual address will access the
physical address 50 (decimal)?

```json
{
  "problem_id": "22",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["minux-tlb"],
  "choices": ["0x0032","0x1023","0x3012","0x3132","None of the above"],
  "answer": "E"
}
```

---

## Question 23 [3 point(s)]

When running on Minux, calculate the hit rate of the TLB assuming a process has 4-KB pages, and
accesses  every 128th byte  on a series of  pages.  Assume  the  TLB  begins  empty,  and  ignore  code
accesses and just focus on this “strided” data access pattern.

```json
{
  "problem_id": "23",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["minux-tlb"],
  "choices": ["Just about 99%","Just about 88%","Just about 50%","Just about 17%","None of the above"],
  "answer": "E"
}
```

---

## Question 24 [3 point(s)]

The  Minux  scheduler  uses  a  new  scheduler  called  “highest  process  ID (PID) first”  (i.e.,  the  job  with
the highest PID always runs, and to completion). Assume job PID=1 arrives at time T=0, with length 10;
PID=2 arrives at T=2, length=6; PID=3 arrives at T=4, with length 4. What is the average response time
of this approach in this example?

```json
{
  "problem_id": "24",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["minux-scheduling"],
  "choices": ["1","2","3","4","None of the above"],
  "answer": "E"
}
```

---

## Question 25 [3 point(s)]

To  reduce  the  size  of  page  tables,  ZOS  combines  the  idea  of  base/bounds  and  paging.  A  virtual
address  space  is  still  chopped  into  pages.  The  page  table  is  pointed  to  by  the  base  register,  and  the
bounds  register  holds  the “size”  of  the  page  table  (really,  the  max  VPN  that  is  valid,  plus  one).  This
approach (choose one):

```json
{
  "problem_id": "25",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["zos-base-bounds"],
  "choices": ["Enables fast translation with only two extra memory references to fetch a PTE","Enables a compact page table, if you use the virtual address space carefully","Is always smaller than a linear page table","Supports a sparse address space while still also minimizing page table memory usage","None of the above"],
  "answer": "B"
}
```

---

## Question 26 [3 point(s)]

ZOS, as mentioned above (Question 25), combines base/bounds and paging. Assume the following:
a 32-bit address space with 1-KB pages. Assume each page table entry (PTE) is 4 bytes. Assume there
are  100  processes  in  the  system.  If  each  process  uses  only  one  virtual  page,  what  is  the  worst-case
total size of all of these page tables?

```json
{
  "problem_id": "26",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["zos-base-bounds"],
  "choices": ["16 MB","160 MB","1600 MB","16 GB","None of the above"],
  "answer": "C"
}
```

---

## Question 27 [3 point(s)]

ZOS uses a new type of scheduler called a proportional-share scheduler. This scheduler makes sure
each  process  gets  a  certain  amount  of  CPU  time,  based  on  how  many  “tickets”  it  has.  For  example,  if
process A has 2 tickets, and process B has 1, A should get twice as much CPU time as B. Note that a
process  cannot  change  how  many  tickets  it  has,  and  all  jobs  only  use  the  CPU  (there  is  no  I/O  in  this
example).  Which  of  the  following  traces  (which  each  show  which  job  was  scheduled  at  each  quantum
over time) does not show the behavior of a proportional-share scheduler?

```json
{
  "problem_id": "27",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["zos-scheduling"],
  "choices": ["AABAABAABAABAA","ABABABABABAB","AAAAAAAAAABBBBB","ABBBABBBABBBABBB","None of the above (they all could be traces from a proportional share scheduler)"],
  "answer": "E"
}
```

---

## Question 28 [3 point(s)]

ZOS  uses  a  new  mechanism  instead  of  timer  interrupts.  Instead  of  interrupting  the  CPU  every  so
many  milliseconds,  the ZOS  hardware  is  programmed  to  interrupt  the  CPU  after  every  N  TLB  misses.
How creative! As compared to the timer, this approach (choose one):

```json
{
  "problem_id": "28",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["zos-tlb-miss"],
  "choices": ["Is equally effective","Is faster to program","Is risky","Requires less memory","Requires virtual memory support"],
  "answer": "C"
}
```

---

## Question 29 [3 point(s)]

A later version of ZOS uses a different, clever approach to sharing the TLB among active processes.
Assume the hardware does not have an address space identifier (or process identifier) field in the TLB.
Instead  of  flushing  the  TLB  when  switching  between  processes,  ZOS  ensures  that  each  process  in  the
system uses different (unique) VPNs as compare to any other process. Which of the following is not true
about this approach:

```json
{
  "problem_id": "29",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["zos-tlb-sharing"],
  "choices": ["Allows for fully flexible use of the virtual address space by each process","Allows for faster context switching (as compared to the TLB flushing approach)","Allows for fully flexible use of physical memory","Allows sharing of code pages between processes","None of the above (all are true)"],
  "answer": "A"
}
```

---

## Question 30 [3 point(s)]

ZOS  also  later  added  support  for  “large”  pages,  a  new  and  clever  idea.  Assume  that  in  a  given
system, regular page size is usually 1 KB, and large pages are 1 MB. When possible, the OS uses large
pages instead of a bunch of smaller ones (e.g., when there is a contiguous, aligned portion of the virtual
address space in use). Why is using large pages a good idea?

```json
{
  "problem_id": "30",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["zos-large-pages"],
  "choices": ["They reduce system complexity","They speed up trap handling","They can increase TLB hit rates","They make physical memory allocation easier","None of the above"],
  "answer": "C"
}
```

---

## Question 31 [3 point(s)]

ZOS also added special hardware, in the form of general-purpose registers that only the kernel can
use.  Indeed,  all  kernel  code  has  been  written  to  only  use  these  registers,  not  the  regular  (user-level)
general purpose ones. Why might these registers for the kernel be a good idea?

```json
{
  "problem_id": "31",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["zos-kernel"],
  "choices": ["Faster trapping into and returning from the kernel","Kernel code now easier to compile","Reduces need for context switching between processes","Now, no way to harm user-level register contents while in kernel code","None of the above"],
  "answer": "A"
}
```

---

## Question 32 [3 point(s)]

Zinus also had this last question for you: which is true about operating systems?

```json
{
  "problem_id": "32",
  "points": 1,
  "type": "ExactMatch",
  "tags": ["os-general"],
  "choices": ["They always make systems run faster","They always make systems use less memory and CPU","They generally make systems easier to use","They never crash","None of the above"],
  "answer": "C"
}
```
