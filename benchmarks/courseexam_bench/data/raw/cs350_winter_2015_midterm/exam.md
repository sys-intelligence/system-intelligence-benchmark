# CS 350 Winter 2015 Midterm

```json
{
  "exam_id": "cs350_winter_2015_midterm",
  "test_paper_name": "CS 350 Winter 2015 Midterm",
  "course": "CS350",
  "institution": "University of Waterloo",
  "year": 2015,
  "score_total": 53,
  "num_questions": 9
}
```

---

## Question 1 [9 point(s)]

For the program shown below, assume that all function, library and system calls are successful. Recall that the prototype/signature forthread
forkis:
int thread_fork(const char *name, struct proc *proc,
void (*func)(void *, unsigned long),
void *data1, unsigned long data2);
volatile int x = 42;
main()
{
/* name="1", no process, runs func1 */
/* parameters 0 and 0, not used */
thread_fork("1",NULL,func1,0,0);
/* name="2", no process, runs func2 */
/* parameters 0 and 0, not used */
thread_fork("2",NULL,func2,0,0);
func3(0,0);
}
void func1(unsigned long notused, void *notused2)
{
kprintf("A: %d\n", x);
x = 10;
}
void func2(unsigned long notused, void *notused2)
{
kprintf("B: %d\n", x);
x = 20;
}
void func3(unsigned long notused, void *notused2)
{
kprintf("C: %d\n", x);
x = 30;
}
When consdering each line of output produced by the program above, what would the output be when
printing the value of the variablex? If more than one value or a range of values is possible, list all possible
values or ranges.
/* From func1 */ A:
/* From func2 */ B:
/* From func3 */ C:
```json
{
  "problem_id": "1",
  "points": 9,
  "type": "Freeform",
  "tags": ["os161", "threads", "concurrency"],
  "answer": "A: 42 | 20 | 30\nB: 42 | 10 | 30\nC: 42 | 10 | 20",
  "llm_judge_instructions": "Award 3 points for each line (A, B, C) as follows. For line A: award 3 points if the student's A line equals one of {42, 20, 30}. For line B: award 3 points if the student's B line equals one of {42, 10, 30}. For line C: award 3 points if the student's C line equals one of {42, 10, 20}. No partial credit for variants not in these sets. Total possible: 9 points."
}
```

---

## Question 2 [14 point(s)]

For the program shown below, what output would be printed when it runs? If a range or multiple values are possible, give the range or possible values. If it is not possible to determine the value, posssible values or a range, state so and explain why. Assume that all function, library and system calls are successful. If more than one ordering of output is possible choose one of the possibleorderings. Recall thatWEXITSTATUS(status)just gets the exit code portion of thestatusvariable.
int x = 42;
main()
{
int rc, status;
rc = fork();
if (rc == 0) {
func1();
_exit(1);
} else {
rc = waitpid(rc, &status, 0);
printf("R: %d", WEXITSTATUS(status));
printf("M: %d\n", x);
x = 100;
printf("P: %d\n", x);
_exit(2);
}
func2();
}
void func1()
{
int rc, status;
printf("T: %d\n", x);
x = 10;
rc = fork();
if (rc == 0) {
x = 50;
printf("Q: %d\n", x);
_exit(3);
}
rc = waitpid(rc, &status, 0)
printf("A: %d\n", x);
printf("D: %d", WEXITSTATUS(status));
_exit(4);
}
void func2()
{
printf("C: %d\n", x);
}
```json
{
  "problem_id": "2",
  "points": 14,
  "type": "Freeform",
  "tags": ["os161", "processes", "fork-wait"],
  "answer": "T: 42\nQ: 50\nA: 10\nD: 3\nR: 4\nM: 42\nP: 100",
  "llm_judge_instructions": "There are seven expected output lines: T, Q, A, D, R, M, P. Award 2 points for each line if the student's line matches exactly one of the expected lines and values: T: 42; Q: 50; A: 10; D: 3; R: 4; M: 42; P: 100. Do not award points for any C line as it does not appear in a valid execution ordering for this program. Total possible: 14 points."
}
```

---

## Question 3 [12 point(s)]

Barrier synchronization can be used to prevent threads fromproceeding until a specified number of threads have reached the barrier. Threads reaching the barrier block until the last of the specified number of threads has reached the barrier, at which point all threads can proceed. Below is a partial pseudocode example of how barrier synchronization might be used.
/* Used to wait for all mice to be ready to all attack together */
struct barrier *attack_barrier;
/* Used to wait for all mice and the main thread so they can all go to the bar together */
struct barrier *bar_barrier;
main()
{
unsigned int i;
attack_barrier = barrier_create(NUM_MICE);
bar_barrier = barrier_create(NUM_MICE+1);
for (i=0; i<NUM_MICE; i++) {
thread_fork("MightyMouse", mouse, NULL, i);
}
/* Wait here until all threads are ready to go to the bar */
barrier_wait(bar_barrier);
go_to_bar();
}
void
mouse(void *unused, unsigned long mouse_num)
{
unsigned int i;
/* Attack the cats a number of times */
for (i=0; i<ATTACK_COUNT; i++) {
get_ammo(mouse_num);
barrier_wait(attack_barrier); /* wait until all mice are ready to attack */
attack_cats();
}
/* Wait here until all threads are ready to go to the bar */
barrier_wait(bar_barrier);
go_to_bar();
}
Fill in the spaces below (or on the next page) to complete the implementation of a barrier. (You will not
implementbarrier
destroy). You must only uselocksandcondition variablesfor synchronization (as
they are defined in OS/161). To simplify the code, assume thatall calls tokmallocand to create any required
objects always succeed.
CS3508 of 13

struct barrier {
};
/* Create a barrier that can be used with thread_count threads */
struct barrier *barrier_create(unsigned int thread_count)
{
}
/* Callers wait here until the number of threads specified have */
/* reached this point, then they all proceed. */
void
barrier_wait(struct barrier *b)
{
}
```json
{
  "problem_id": "3",
  "points": 12,
  "type": "Freeform",
  "tags": ["barrier", "concurrency", "synchronization"],
  "answer": "struct barrier {\n/* This MUST be volatile */\nvolatile unsigned int b_threads_reached;   /* how many have reached the barrier */\n/* This does not need to be volatile, only changed by one thread at init time */\nunsigned int b_threads_expected;           /* num threads to wait for*/\nstruct lock *b_lock;                       /* lock used to protect count and reached */\nstruct cv *b_cv;                           /* cv used to wait when needed */\n};\nstruct barrier *barrier_create(unsigned int thread_count)\n{\nstruct barrier *b = (struct barrier *) kmalloc(sizeof(struct barrier));\nb->b_lock = lock_create(\"barrier\");\nb->b_cv = cv_create(\"barrier\");\nb->b_threads_expected = thread_count;\nb->b_threads_reached = 0;\nreturn b;\n}\nvoid barrier_wait(struct barrier *b)\n{\nlock_acquire(b->b_lock);\nb->b_threads_reached++;\nif (b->b_threads_reached == b->b_threads_expected) {\n/* Must reset number of threads reached to use the barrier more than once */\nb->b_threads_reached = 0;\ncv_broadcast(b->b_cv, b->b_lock);\n} else {\ncv_wait(b->b_cv, b->b_lock);\n}\nlock_release(b->b_lock);\n}",
  "llm_judge_instructions": "Grade with the following explicit rubric (total 12 pts): barrier_create (4 pts): 1 pt for allocating the struct (non-NULL return), 1 pt for creating/assigning the lock, 1 pt for creating/assigning the cv, 1 pt for setting b_threads_expected and initializing b_threads_reached to 0. barrier_wait (8 pts): 2 pts for acquiring the lock and incrementing the counter correctly, 2 pts for implementing the 'last thread' path that resets the counter and does a broadcast, 2 pts for implementing the waiting path using cv_wait, 2 pts for releasing the lock and ensuring correctness for reuse of the barrier. Award partial credit only for the components listed above."
}
```

---

## Question 4 [3 point(s)]

The physical address that results from a load from virtual address = 6 125 273 127 604
```json
{
  "problem_id": "4",
  "points": 3,
  "type": "Freeform",
  "tags": ["virtual-memory", "tlb", "paging"],
  "answer": "THIS DOES NOT NEED TO BE STATED OR REPEATED FOR THIS PART.\n$2^{18}$ = 256 KB so 18 bits for offset. 39-18 = 21 for VPN.\n18 bits = 6 octal characters for offset, 21 bits = 7 octal characters for VPN.\nSo the first 7 octal characters are the VPN and the last 6 are the offset.\n612 5273 | 127 604\nlookup 612 5273 in TLB valid bit is NOT set so exception.",
  "llm_judge_instructions": "Award 3 points for a correct answer identifying that the TLB lookup results in a TLB miss/exception because the valid bit is not set. If the student correctly splits the VPN and offset but does not conclude the exception, award 1-2 points (2 pts for correct VPN/offset split, 1 pt for indicating a TLB lookup occurred). Total possible: 3 pts."
}
```

---

## Question 5 [3 point(s)]

The physical address that results from a store to virtual address = 0 000 061 252 127.
```json
{
  "problem_id": "5",
  "points": 3,
  "type": "Freeform",
  "tags": ["virtual-memory", "tlb", "paging"],
  "answer": "0 000 061 | 252 127.\n0 000 061 is in the TLB and is valid and can be dirtied so translation occurs.\nResulting frame is 30 130.\nSo resulting address is 30 130 252 127.",
  "llm_judge_instructions": "Award 3 points total: 2 points for the correct final physical address 30 130 252 127, and 1 point for correctly stating that the TLB entry is a hit and allows the page to be dirtied. Partial credit: 1 point for correct justification or correct final address only."
}
```

---

## Question 6 [3 point(s)]

Can a store be performed on thephysicaladdress = 61 252 612 522 If yes, provide the
virtual address used to access this physical address and if not explain precisely why not.
```json
{
  "problem_id": "6",
  "points": 3,
  "type": "Freeform",
  "tags": ["virtual-memory", "tlb", "paging"],
  "answer": "61 252 612 522 frame is 61 252 which is found in the TLB.\nThe page can be written and is valid so a translation occurs.\nThe corresponding page is 0 000 612 so we get the virtual address\n0 000 612 612 522",
  "llm_judge_instructions": "Award 3 points if the student shows the physical frame and offset mapping and provides the virtual address 0 000 612 612 522 with justification that the TLB entry is valid and writable. Award 2 points for correct virtual address without full justification, 1 point for correct justification without exact virtual address."
}
```

---

## Question 7 [3 point(s)]

Note: to make some numbers easier to read, spaces have been added between every 4 hexidecimal characters.
Please also use this convention when providing your answers.
The structureaddrspaceshown below describes the address space of a running processon a slightly modified
MIPS processor.  Theaddrspaceand modified processor are similar to thedumbvmand MIPS processor
provided in OS161/SYS161.  The key differences are that this processor uses 36-bit virtual and physical
addresses and a page size of 64 KB (0x1 0000). In a similar fashion to the 32-bit MIPS OS/161 processor the
36-bit virtual address space on this modified processor is divided into two halves. Virtual addresses from0to
0x7 FFFF FFFFare for user programs and virtual address from0x8 0000 0000to0xF FFFF FFFFcan not be
accessed while in user mode. Fortunately, this new version of the OS161 kernel now explicitly represents the stack as segment 3 (note the stack size).
struct addrspace {
vaddr_t as_vbase1 = 0x0 5000 0000;      /* text segment: virtual base address */
paddr_t as_pbase1 = 0x0 0010 0000;      /* text segment: physicalbase address */
size_t as_npages1 = 0x200;              /* text segment: number of pages */
vaddr_t as_vbase2 = 0x3 0000 0000;      /* data segment: virtual base address */
paddr_t as_pbase2 = 0x8 0000 0000;      /* data segment: physicalbase address */
size_t as_npages2 = 0x137;              /* data segment: number of pages */
vaddr_t as_vbase3 = 0x4 0000 0000;      /* stack segment: virtualbase address */
paddr_t as_pbase3 = 0x1 0000 0000;      /* stack segment: physical base address */
size_t as_npages3 = 0x18;               /* stack segment: number of pages */
};
For an application executing in user space that uses the address space defined above, assume that it is accessing
the specified addresses below. When possible you are to translate the provided address. If the translation
is not possible, explain why it is not possible and what wouldhappen during translation. If the translation
is possible provide the requested translated address and indicate which segment the address belongs to. Use
hexadecimal notation for all addresses and show all 36-bits. Show and explain how you arrived at your result.
Some possibly useful values:
1 * 64 KB =  0x1 * 0x1 0000 =  0x1 0000    2 * 64 KB =  0x2 * 0x1 0000 = 0x2 0000
10 * 64 KB = 0xA * 0x1 0000 = 0xA 0000   16 * 64 KB = 0x10 * 0x1 0000 = 0x10 0000
32 * 64 KB = 0x20 * 0x1 0000 = 0x20 0000
a.(3 point(s))Translate theVirtualAddress0x4 0017 6429to aPhysicalAddress.
```json
{
  "problem_id": "7",
  "points": 3,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging", "mips"],
  "answer": "Part of the stack segment.\n0x4 0017 6429 - 0x4 0000 0000 = 0x17 6429 (this is < 0x18 pages, 0x18 0000)\nSo 0x17 6429 + 0x1 0000 0000 = 0x1 0017 6429",
  "llm_judge_instructions": "Award 3 points if the student identifies the address as in the stack segment and computes the physical address 0x1 0017 6429 with correct arithmetic. Award 2 points for correct numeric translation without clear segment identification, 1 point for correct segment identification with an arithmetic error."
}
```

---

## Question 8 [3 point(s)]

b.(3 point(s))Translate theVirtualAddress0x0 5200 AB25to aPhysicalAddress.
```json
{
  "problem_id": "8",
  "points": 3,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging", "mips"],
  "answer": "No translation. This is not part of ANY segment.",
  "llm_judge_instructions": "Award 3 points if the student clearly states the virtual address 0x0 5200 AB25 is not within any defined segment and explains that the translation will fault (address not mapped). Award 1-2 points for partial reasoning (1 point for stating 'not in segment' without correct explanation, 2 points for correct segment check but missing the fault explanation)."
}
```

---

## Question 9 [3 point(s)]

c.(3 point(s))If possible, determine the user spaceVirtualAddress that could be used to access the
PhysicalAddress0x8 0128 95FA.
```json
{
  "problem_id": "9",
  "points": 3,
  "type": "Freeform",
  "tags": ["virtual-memory", "paging", "mips"],
  "answer": "Part of the data segment.\n0x8 0128 95FA - 0x8 0000 0000 = 0x128 95FA (0x128 95FA < 0x137 pages = 0x137 0000).\nSo 0x128 95FA + 0x3 0000 0000 = 0x3 0128 95FA.",
  "llm_judge_instructions": "Award 3 points if the student identifies the data segment and computes the corresponding user virtual address 0x3 0128 95FA with correct justification. Award 2 points for correct arithmetic without explicit segment explanation, 1 point for correct segment identification without full arithmetic."
}
```