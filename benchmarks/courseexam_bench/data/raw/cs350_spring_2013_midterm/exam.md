# CS350 Spring 2013 Midterm

```json
{
  "exam_id": "cs350_spring_2013_midterm",
  "test_paper_name": "CS350 Spring 2013 Midterm",
  "course": "CS350",
  "institution": "University of Waterloo",
  "year": 2013,
  "score_total": 33,
  "num_questions": 4
}
```

---

## Question 1 [12 point(s)]

Explain why the following statements are true or false. If a subpart requires a justification, provide a concise explanation.

(a) Explain why registers k0 & k1 cannot be used (even temporarily) by gcc in OS/161.

(b) Explain why there are more registers stored in a trap frame than in a thread context.

(c) True or false: If there are no global variables, then no locks are necessary. Briefly justify your answer.

(d) Give one advantage and one disadvantage of having a software design with high lock granularity (many locks).

(e) Briefly explain what this line of code is doing and why: tf->tf_v0 = retval; in a MIPS syscall handler context.

(f) Briefly describe why the C stdio library binary is not portable between different operating systems, even on the same hardware (machine architecture).

(g1) Explain the primary difference (as discussed in class) between Hoare semantics and the Mesa semantics used in OS/161.

(g2) A system uses a dynamic relocation virtual address scheme. The virtual addresses are 16 bits long, but the relocation register is 32 bits long. What is the maximum amount of physical memory that can be made available to each process? How much physical RAM can the entire system support?

(h) What is the difference between internal and external memory fragmentation?

(i) Explain why dumbvm is more like dynamic relocation than paging.

(j) Give one advantage and one disadvantage of having a small quantum.

(k) Explain the significance of the return value of fork().

```json
{
  "problem_id": "1",
  "points": 12,
  "type": "Freeform",
  "tags": ["operating-systems", "os-161", "concurrency"],
  "answer": "a) k0 & k1 are reserved for the kernel/exception handling and can be overwritten by the kernel before or during trap handling; user-level compilers like gcc must not assume they are callee-saved. b) Trap frames must save nearly all registers because traps can happen asynchronously (from user context) and the kernel cannot rely on caller/callee conventions; thread contexts are saved/restored at well-defined points where some temporary registers need not be preserved. c) False. Locks protect any shared resource, not just globals; even without globals threads can share heap data, file descriptors, devices, etc., so locks may still be required. d) Advantage: finer-grained locks allow more concurrency and parallelism. Disadvantage: increased locking overhead and greater complexity, including higher risk of deadlock. e) This stores the syscall return value into the trapframe's v0 register so that when control is returned to user mode, the user process sees the syscall's return value in register v0. f) Binaries depend on OS-specific ABI details (syscall numbers, calling conventions, dynamic loader behavior, library paths), so a stdio binary built for one OS will generally not run unchanged on another. g1) Hoare semantics: a signaler hands control immediately to the waiting thread (the waiter runs immediately); Mesa semantics (used in OS/161): the signaler continues and the waiter is merely made runnable and must re-acquire the condition/lock later. g2) Per-process virtual address space is 2^16 = 65536 bytes (64 KB). With a 32-bit relocation register, physical addresses can span 2^32 bytes = 4 GiB, so the system could address up to 4 GiB of RAM total. h) Internal fragmentation is wasted space within allocated regions (e.g., due to fixed-size blocks/pages leaving unused bytes); external fragmentation is wasted space because free regions are split into small noncontiguous holes that cannot satisfy larger allocation requests. i) dumbvm uses contiguous segments and simple base relocation (storing segment base addresses) rather than page tables and noncontiguous page mappings, so it behaves like dynamic relocation. j) Small quantum: advantage — improved responsiveness and lower latency for interactive tasks; disadvantage — higher context-switch overhead and lower CPU efficiency due to more frequent switching. k) fork() returns 0 in the child and the child's PID (positive integer) in the parent; this lets code distinguish parent from child and perform different actions.",
  "llm_judge_instructions": "There are 12 subitems in this question (a, b, c, d, e, f, g1, g2, h, i, j, k). Award 1 point for each subitem answered correctly with an appropriate concise justification. Total = 12 points. If a subitem is missing or incorrect, award 0 for that subitem. Provide brief comment per subitem indicating correctness."
}
```

---

## Question 2 [6 point(s)]

Given the following MIPS 64-bit TLB entry specification (with 4k page sizes)

VPAGE  bits  44-63 
PFRAME bits 12-31 
DIRTY  bit   10 
VALID  bit    9

and the following TLB entries (Most Significant Bit on the left):

0x0000000000006600
0x0000100000002200
0x0012300045645600
0x0040000000400400
0x1000000010000600

a) For each virtual address below, give the corresponding physical address. If it cannot be determined or a fault would occur reading the address, write "FAULT".

List of virtual addresses:
- 0x00000006
- 0x00006006
- 0x10000001
- 0x00123456
- 0x45645645
- 0x00001234
- 0x00400040
- 0x80123456

b) For each physical address, provide the corresponding virtual address. If it cannot be determined, write "UNKNOWN".

List of physical addresses:
- 0x00000006
- 0x10000001
- 0x45645645
- 0x00400040
- 0x80123456

```json
{
  "problem_id": "2",
  "points": 6,
  "type": "Freeform",
  "tags": ["virtual-memory", "tlb", "memory-management"],
  "answer": "a) Mappings: 0x00000006 -> 0x00006006; 0x00006006 -> 0x00006006 (same mapping shown); 0x10000001 -> 0x10000001; 0x00123456 -> 0x45645456 (as derived from the matching TLB entry); 0x45645645 -> FAULT; 0x00001234 -> 0x00002234; 0x00400040 -> FAULT (invalid); 0x80123456 -> 0x00123456. b) Reverse mappings: 0x00000006 -> UNKNOWN (multiple virtual pages could map here or none); 0x10000001 -> 0x10000001; 0x45645645 -> 0x00123645 (derived virtual that maps to that physical frame); 0x00400040 -> UNKNOWN; 0x80123456 -> UNKNOWN.",
  "llm_judge_instructions": "There are 12 mappings to check (8 in part a, 5 in part b but one overlaps). Award 0.5 points for each correctly identified mapping/outcome (mapping to physical address, 'FAULT', or 'UNKNOWN') for a total of 6 points. Provide brief comment for any incorrect/missing mapping."
}
```

---

## Question 3 [8 point(s)]

(a) [4 Marks] Give a proof as to why resource ordering can prevent deadlocks. It can be informal, but it should be sound. You are not required to reference the deadlock detection algorithm, but you may reference it if you choose.

(b) [4 Marks] Here is Peterson’s algorithm as presented in class. Your friend has implemented Peterson’s algorithm for OS/161 as follows:

turn = 1 - tid;
flag[tid] = 1;
while (turn != tid && flag[1 - tid]) { }
/* critical section */
flag[tid] = 0;

Describe how the critical section is protected (or not protected) in this implementation. Justify your answer.

```json
{
  "problem_id": "3",
  "points": 8,
  "type": "Freeform",
  "tags": ["deadlock", "concurrency", "petersons-algorithm"],
  "answer": "(a) Proof sketch: With a global strict ordering on resources, each thread must acquire resources in increasing order. A cycle in the resource-allocation graph would require a strictly increasing sequence of resource ranks that returns to the starting resource, which is impossible. Hence cycles (and deadlock) cannot occur. (b) The provided implementation is incorrect: setting turn before flag[tid] can allow both threads to see turn in a state that permits entering the critical section, violating mutual exclusion. The correct Peterson sequence sets flag[tid] before writing turn, and the while condition should wait while (flag[other] && turn == other); as written the ordering permits a race where both threads enter.",
  "llm_judge_instructions": "Award up to 4 points for part (a): 4 pts for a correct, logically sound explanation that shows why a strict resource ordering eliminates cycles; partial credit up to 2 pts for an incomplete but correct insight. Award up to 4 points for part (b): 4 pts for correctly identifying the ordering bug and explaining why mutual exclusion fails, up to 2 pts for a partially correct explanation. Provide brief comments for partial credit."
}
```

---

## Question 4 [7 point(s)]

(a) [2 Marks] Concisely explain how in your A1 cat/mouse solution the decision was made to switch from allowing one animal to eat (i.e., cats) to the other animal eating (i.e., mice). If you did not complete assignment 1, describe the naïve solution discussed in class.

(b) [1 Mark] Given the above specifications and that (c >> b) and (m >> b), describe any circumstances under which your solution described in (a) would achieve its maximum efficiency, and then calculate that efficiency as a formula using the variables c, m, b and t as necessary.

(c) [4 Marks] Given the above specifications, consider the following solution: "Allow k mice to eat, then allow k cats to eat, and then allow k mice to eat, and so on..." Determine the efficiency for each scenario below. For each scenario, give the maximum wait time for both cats and mice (the time from when a given cat finishes eating until that cat next starts eating). Assume fairness among animals of the same type: once cat X eats, all other cats eat exactly once before cat X eats again.

Scenarios (parameters c, m, b, t, k):
1) c = 10, m = 5, b = 5, t = 1, k = 5
2) c = 10, m = 10, b = 5, t = 1, k = 5
3) c = 10, m = 10, b = 50, t = 25, k = 5
4) c = 25, m = 10, b = 11, t = 9, k = 10

For each scenario compute:
- Efficiency (fraction of time bowls are in use)
- Maximum wait time for Cats
- Maximum wait time for Mice

```json
{
  "problem_id": "4",
  "points": 7,
  "type": "Freeform",
  "tags": ["cat-mouse", "concurrency", "synchronization"],
  "answer": "(a) The decision was based on a policy that allows a bounded number of consecutive eaters of one species before switching to the other to prevent starvation and improve throughput; the naive solution would let one species eat indefinitely, which can starve the other. (b) Maximum efficiency occurs when bowl turnover and scheduling produce no idle time between eaters; with c >> b and m >> b and negligible switching overhead, efficiency approaches 1 (i.e., bowls almost always in use). The precise formula depends on how many bowls are used in parallel and the switching overhead; in the ideal alternating steady state efficiency = useful eating time / total time. (c) For each scenario compute efficiency and max wait times based on k, b, t, c, m and the scheduling described. (Full numeric answers depend on following the outlined calculation for each scenario.)",
  "llm_judge_instructions": "(a) 2 pts: award 1 pt for describing the switching decision mechanism and 1 pt for justification (preventing starvation/improving throughput). (b) 1 pt: award for identifying circumstances and deriving a correct formula or clear expression. (c) 4 pts total: 1 point per scenario. For each scenario, award the 1 point if the student provides the correct efficiency and both correct maximum wait times; award 0.5 if some but not all of those three values are correct with clear reasoning. Provide brief annotations for partial credit. Total = 7 points."
}
```