# CS350 Fall 2015 Midterm

```json
{
  "exam_id": "cs350_fall_2015_midterm",
  "test_paper_name": "CS350 Fall 2015 Midterm",
  "course": "CS 350",
  "institution": "University of Waterloo",
  "year": 2015,
  "score_total": 68,
  "num_questions": 7
}
```

---

## Question 1 [12 point(s)]

Consider the following code fragments that use semaphores:

```c
/* Initialization (executed once by initial thread) */
struct semaphore *sa;
struct semaphore *sb;
struct semaphore *sc;

sa = semcreate("A", 1);
sb = semcreate("B", 1);
sc = semcreate("C", 0);

/* Threads run these functions */
void func1() {
    P(sa);
    funcA();
    V(sa);
    P(sc);
}

void func2() {
    P(sb);
    funcB();
    V(sb);
    V(sc);
}
```

In the space below, re-implement func1 and func2 without using semaphores. Instead, use locks and condition variables for synchronization. Your re-implemented functions must have the same behavior as the original functions shown above. You may create as many locks, condition variables, and other global variables as you need. Be sure to show global variable declarations and initialization, as well as the implementations of func1 and func2.

```c
/* Provide your global declarations, initialization, and the implementations
   of func1 and func2 here. */

/* Example placeholder:
struct lock *la;
struct lock *lb;
struct lock *lc;
struct cv *cv;
int some_counters;

void func1() {
    // ...
}

void func2() {
    // ...
}
*/
```

---

## Question 2 [10 point(s)]

a. (2 marks)  
What is the maximum number of entries in a page table in this system?

b. (4 marks)  
A process P1 has the following page table. Frame numbers are given in hexadecimal notation.

Page Number | Frame Number
--- | ---
0x0 | 0x1010
0x1 | 0x2034
0x2 | 0x43AC
0x3 | 0x1100
0x4 | 0xAC11
0x5 | 0x8000

For each of the following physical addresses, indicate the virtual address to which it maps. If the physical address is not part of the physical memory assigned to P1, write NO TRANSLATION instead. Use hexadecimal notation for the virtual addresses.

- 0x1100A0
- 0xAC1100
- 0xBA3424
- 0x43ACA0
- 0x3A0
- 0x400
- NO TRANSLATION
- 0x2A0

c. (2 marks)  
Due to a bug in the OS/161 as copy function, the following is the page table of P1’s child process immediately after it returns from fork. Mark the entries in the page table that you are certain to be incorrect.

Page Number | Frame Number
--- | ---
0x0 | 0x2453
0x1 | 0x1010
0x2 | 0xEA35
0x3 | 0x3100
0x4 | 0x2034
0x5 | 0x9012

d. (2 marks)  
Name one advantage and one disadvantage of having a virtual address space that is smaller than the physical address space.

---

## Question 3 [8 point(s)]

```c
void bump() {
    int y;
    x++; // x is a global variable
    y = x;
    kprintf("%d", y); // print value of y
}
```

Assume that x is a volatile integer global variable, and that its value is initialized to 0 before any calls to bump. Suppose that the bump function is part of a concurrent program that uses k concurrent threads, and that each thread calls bump one time. Assume that calls to kprintf are atomic (kprintf uses a lock to ensure that threads will print one at a time).

a. (6 marks)  
Suppose that this concurrent program is running on a machine with one single-core processor, and that k = 4. Which of the following outputs are possible for this program? For each output, write “yes” if it is possible, and “no” if it is not possible.

- 1234
- 4321
- 0123
- 2222
- 4444
- 1235
- 012
- 1124

b. (2 marks)  
Suppose instead that the concurrent program (with k = 4) runs on a machine with two single-core processors. Do your answers from part (a) change? If not, write “No Change”. If so, indicate one output string from part (a) for which you would give a different answer in this situation.

---

## Question 4 [8 point(s)]

Virtual Address | Physical Address
--- | ---
0x0008 0AF0 | 0x0010 1AF0
0x0000 2224 | 0x0008 3224
0x0007 3234 | 0x0018 3234

Suppose that while a process P is running, it uses the virtual addresses shown in the left column of the table above. For each of these virtual addresses, the corresponding physical address (after address translation) is also shown in the table. On the machine on which P is running, both virtual addresses and physical addresses are 32 bits long.

a. (3 marks)  
Given the virtual-to-physical address translations shown in the table, is it possible that the MMU used dynamic relocation to translate P’s virtual addresses to physical addresses? If so, write “YES” and indicate the value that must be in the MMU’s relocation register while P is running. If not, write “NO” and explain briefly and clearly how you know that dynamic relocation was not used.

b. (3 marks)  
Is it possible that the MMU used paging, with a page size of 64 KB (2^16 bytes), to translate P’s virtual addresses to physical addresses? If so, write “YES”. If not, write “NO” and explain briefly and clearly how you know that paging with this page size was not used.

c. (2 marks)  
Is it possible that the MMU used paging, with a page size of 4 KB (2^12 bytes), to translate P’s virtual addresses to physical addresses? If so, write “YES”. If not, write “NO” and explain briefly and clearly how you know that paging with this page size was not used.

---

## Question 5 [8 point(s)]

a. (3 marks)  
Is it possible for a thread’s kernel stack to contain more than one trap frame? If yes, write “YES” and identify — clearly and briefly — a situation in which this could occur. If not, write “NO”.

b. (2 marks)  
Is it possible that a call to OS/161’s wchan_sleep function will cause a thread context switch? Answer “YES” or “NO” and briefly explain your answer. (Answers without a clear explanation will receive no credit.)

c. (2 marks)  
Each page table entry normally includes a valid bit. Explain, briefly and clearly, the purpose of a valid bit. What happens if a process attempts to access a virtual address on a page that is mapped by an invalid page table entry (i.e., one for which the valid bit is not set)? Explain briefly and clearly.

d. (1 mark)  
When a system call occurs in OS/161, how does the kernel know which system call has been requested? Explain briefly and clearly.

---

## Question 6 [10 point(s)]

a. (3 marks)  
List the different transitions between the three thread states (Ready, Running, Blocked). Why can’t a thread go from a Blocked state directly to a Running state?

b. (2 marks)  
Explain the difference between a trapframe and a switchframe. What generates a trapframe? What generates a switchframe?

c. (3 marks)  
Describe a scenario (list of steps) in which having spinlock_release(&sem->semlock) before wchan_lock(sem->semwchan) in the semaphore P() implementation can cause a concurrency problem.

d. (2 marks)  
What information can be found in each TLB entry?

---

## Question 7 [12 point(s)]

You have been hired by Snowflake Entertainment to design the matchmaking system for their new multiplayer online game. In this game, a match consists of 3 players and can only start when all 3 players are available. The company owns only one server and the server can only host one match at a time. A new match can start on the server only when (a) the previous match has finished, and (b) three players are available to play.

Implement the following three functions to satisfy the specified constraints. Global variables can be defined in the provided space.

```c
#define PLAYERS_PER_MATCH 3

/* Define your global variables here. */
/* Example placeholder:
struct lock* match_lock;
struct cv* match_cv;
int num_waiting;
int num_in_game;
*/

/* Called only once before any players have arrived. */
void gamesync_init() {
    /* Initialize your globals here */
}

/* Called only once when the company takes down the system for maintenance. */
void gamesync_cleanup() {
    /* Cleanup your globals here */
}

/* Called once by each player, before that player starts a match.
   Should block until the player's match can start (according to
   Snowflake's synchronization requirements). */
void before_match() {
    /* Implement synchronization so that players block until a match of
       PLAYERS_PER_MATCH can start on the single server. */
}

/* Called once for each player, after that player's match is finished. */
void after_match() {
    /* Implement synchronization to update state and potentially wake
       waiting players for the next match. */
}
```

Provide your global variables, initialization, cleanup, and the implementations of before_match and after_match.