# CS 350 Midterm Spring 2013

```json
{
  "exam_id": "cs530_spring_2013_midterm",
  "test_paper_name": "CS 350 Midterm Spring 2013",
  "course": "CS530",
  "institution": "University of Waterloo",
  "year": 2013,
  "score_total": 42,
  "num_questions": 9
}
```

---

## Question 1 [12 Point(s)]

Explain the following subparts from CS350 Midterm Spring 2013, Question 1 (a) through (k).

```json
{
  "problem_id": "1",
  "points": 12,
  "type": "Freeform",
  "tags": ["operating-systems", "os-kernel", "trapframes", "concurrency"],
  "answer": "a) k0 & k1 are overwritten by the kernel by the exception (interrupt) handler before the trap frame is stored.\n\nb) Trap frames happen unexpectedly and must store (almost) all registers. Thread contexts occur purposefully and within functions (\"subroutines\"), so temp registers that are not preserved by subroutines do not have to be stored.\n\nc) False. Locks protect other resources (not just memory). Also, there can be heap memory that is shared between threads.\n\nd) Advantage: better concurrency. Disadvantage: more overhead, greater chance of deadlock.\n\ne) This modifies the trap frame so when the user process resumes it can access the return value of the system call (in register v0).\n\nf) Each OS has its own conventions for enumerating system calls (and using registers).\n\ng) In Hoare semantics, when a thread signals it immediately releases the lock. In Mesa semantics, threads retain the lock after signaling.\n\nh) A system uses a dynamic relocation virtual-address scheme. The virtual addresses are 16 bits long, but the relocation register is 32 bits long. What is the maximum amount of physical memory that can be made available to each process? How much physical RAM can the entire system support?\n\n64KB & 4GB\n\ni) What is the difference between internal and external memory fragmentation.\n\ninternal: (paging) the minimum unit of memory allocated to a process is a page. When less than a page is required, that memory is \"wasted\".\n\nexternal: (dynamic relocation) all memory allocations must be contiguous. When there are blocks of unallocated space between allocations that are too small to be used, that memory is \"wasted\".\n\nj) Explain why dumbvm is more like dynamic relocation than paging.\n\nLike dynamic relocation, dumbvm requires its segments to be contiguous in memory – for each segment it only stores the starting location in physical memory (not a page table).\n\nk) Give one advantage and one disadvantage of having a small quantum.\n\nadvantage: OS is more responsive.\n\ndisadvantage: more overhead due to context switching.",
  "llm_judge_instructions": "Award 1 point for each correct item a) through k) (11 points). Award an extra 1 point if all parts a) through k) are correct. Total 12 points."
}
```

---

## Question 2 [6 Points]

Given the following MIPS 64-bit TLB entry specification (with 4k page sizes)

VPAGE  bits  44-63 
PFRAME bits  12-31 
DIRTY  bit   10 
VALID  bit    9 

and the following TLB entries:

0x 0000 0000 0000 6600 
0x 0000 1000 0000 2200 
0x 0012 3000 4564 5600 
0x 0040 0000 0040 0400 
0x 1000 0000 1000 0600 

a) For each virtual address below, give the corresponding physical address. If it cannot be determined or a fault would occur reading the address, write “FAULT”.

```json
{
  "problem_id": "2-a",
  "points": 3,
  "type": "Freeform",
  "tags": ["tlb", "virtual-memory", "address-translation"],
  "answer": "0x0000 0006 -> 0x0000 6006; 0x1000 0001 -> 0x1000 0001; 0x0012 3456 -> 0x4564 5456; 0x4564 5645 -> FAULT; 0x0000 1234 -> 0x0000 2234; 0x0040 0040 -> FAULT; 0x8012 3456 -> 0x0012 3456",
  "llm_judge_instructions": "Award 1 point for each correctly computed mapping, up to a maximum of 3 points."
}
```

b) For each physical address, provide the corresponding virtual address. If it cannot be determined, write “UNKNOWN”.

```json
{
  "problem_id": "2-b",
  "points": 3,
  "type": "Freeform",
  "tags": ["tlb", "virtual-memory", "address-translation"],
  "answer": "0x0000 0006 -> UNKNOWN (could map from multiple VPNs such as 0x0000, 0x8000, 0xA000, etc.); 0x1000 0001 -> 0x1000 0001; 0x4564 5645 -> 0x0012 3645; 0x0040 0040 -> UNKNOWN; 0x8012 3456 -> UNKNOWN",
  "llm_judge_instructions": "Award 1 point for each correct virtual address mapping up to a maximum of 3 points. If the physical address cannot be uniquely inverted to a single virtual address, awarding UNKNOWN is acceptable."
}
```

---

## Question 3 [8 Points]

(a) [4 Points] Give a proof as to why resource ordering can prevent deadlocks. It can be informal, but it should be sound. You are not required to reference the deadlock detection algorithm, but you may reference it if you choose.

Aside: resource ordering requires a total order (ie: positive integers) which requires that each resource must have a unique value, and there can be no “duplicates”. In the problems we study with duplicate resources, they can be simply enumerated as separate resources.

Proof by contradiction:

Claim: There exists a deadlock.

With unique resources, any deadlock will correspond to a “cycle” in the resource allocation graph. We will enumerate the threads and resources in the cycle:

T1 -> R1 -> T2 -> R2 -> ... RN-1 -> TN -> RN -> T1 -> R1 ...

With resource ordering, each thread must acquire resources in ascending order. Therefore,

R1 < R2 and R2 < R3 ... RN-1 < RN and RN < R1 if R1 < R2 < R3 ... RN-1 < RN then R1 < RN

We have a contradiction: RN < R1 and R1 < RN

Therefore, original claim is false. A deadlock cannot exist.

```json
{
  "problem_id": "3-a",
  "points": 4,
  "type": "Freeform",
  "tags": ["deadlock", "resource-ordering", "theory"],
  "answer": "Assume for contradiction that a deadlock exists. Then there is a cycle in the resource-allocation graph: T1 holds R1 and waits for R2, T2 holds R2 and waits for R3, ..., TN holds RN and waits for R1. Resource ordering requires every thread to acquire resources in strictly increasing order (according to a global total order). Thus if T1 waits for R2 after holding R1, we must have R1 < R2; similarly R2 < R3; ...; RN < R1. Chaining these inequalities gives R1 < R2 < ... < RN < R1, which is impossible. Hence the assumption of a deadlock (cycle) leads to a contradiction, so no deadlock can occur when all threads acquire resources in a global increasing order.",
  "llm_judge_instructions": "Allocate points as follows: 1 point for stating that resource ordering imposes a total/global order on resources; 1 point for assuming a cycle and enumerating a sequence of threads/resources that form the cycle; 1 point for deriving the chain of inequalities (R1 < R2 < ... < RN < R1); 1 point for pointing out the contradiction and concluding that deadlock cannot exist. Total 4 points."
}
```

(b) [4 Points] Here is Peterson’s algorithm as presented in class:

volatile boolean flag[2]; // initially false 
volatile int turn; 
// for thread A: i = 0 & j = 1, thread B: i = 1 & j = 0 

flag[i] = true; 
turn = j; 
while (flag[j] && turn == j) { } 
//critical section 
flag[i] = false; 

Your friend has implemented Peterson’s algorithm for OS/161 as follows:
(He used a thread id tid to identify each thread: tid has the value of either 0 or 1)

turn = 1 - tid; 
flag[tid] = 1; 
while (turn != tid && flag[1 - tid]) { } 
//critical section 
flag[tid] = 0; 

Describe how the critical section is protected (or not protected) in this implementation. Justify your answer.

```json
{
  "problem_id": "3-b",
  "points": 4,
  "type": "Freeform",
  "tags": ["synchronization", "peterson", "mutual-exclusion"],
  "answer": "The implementation is NOT correct and can fail to provide mutual exclusion. The two assignments are swapped compared to the canonical Peterson sequence. In the correct algorithm a thread first sets its flag and then sets turn = other, ensuring that if the other thread also sets its flag, turn will determine who waits. In the buggy version the thread sets turn = other first and then sets its own flag; this can create an interleaving where both threads set turn to the other and both set their flag so that both enter the while loop condition in a way that allows both to proceed into the critical section (race on the order of writes). Thus mutual exclusion can be violated.",
  "llm_judge_instructions": "Award 2 points for correctly identifying that the assignment order is swapped and that this is the bug. Award 1 point for explaining why swapping the assignments can break the protocol (give a small interleaving argument or description). Award 1 point for concluding that mutual exclusion is not guaranteed. Total 4 points."
}
```

---

## Question 4 [7 Points]

(a) [2 Points] Concisely explain how in your A1 cat/mouse solution the decision was made to switch from allowing one animal to eat (i.e., cats) to the other animal eating (i.e., mice). If you did not complete assignment 1, describe the naïve solution discussed in class.

(depends on assignment implementation)

```json
{
  "problem_id": "4-a",
  "points": 2,
  "type": "Freeform",
  "tags": ["synchronization", "analysis", "cs530"],
  "answer": "Depends on the student's implementation. Example: switch when either the current species has no more waiting animals or a fairness counter reaches a threshold; naive solution: alternate strictly after each animal or after a fixed time slice.",
  "llm_judge_instructions": "Award 1 point for clearly describing the decision mechanism used (or the naive solution). Award 1 point for providing a concise justification for that choice (e.g., fairness, throughput). Total 2 points."
}
```

(b) [1 Point] Given the above specifications and that (c >> b) and (m >> b), describe any circumstances under which your solution described in (a) would achieve its maximum efficiency, and then calculate that efficiency as a formula using the variables c, m, b and t as necessary. Trivial solution: MOST solutions would achieve maximum efficiency (1) when there is only one bowl.

```json
{
  "problem_id": "4-b",
  "points": 1,
  "type": "Freeform",
  "tags": ["efficiency", "cs530", "synchronization"],
  "answer": "Efficiency is maximized when contention is minimized; for example, if b=1 and arrivals are well-ordered such that the bowl is always in use, efficiency approaches 1. Formula example: efficiency = min(1, (number_of_animals_eating_simultaneously)/b), which equals 1 when b >= animals_eating.",
  "llm_judge_instructions": "Award 1 point for stating that efficiency is maximized when b=1 (or when bowls are fully utilized) and providing a brief formula or explanation showing the fraction of bowls in use approaches 1 under that condition."
}
```

(c) [4 Points] Given the above specifications, consider the following solution: “Allow k mice to eat, then allow k cats to eat, and then allow k mice to eat, and so on...” Determine the efficiency for each scenario below. For each scenario, give the maximum wait time for both cats and mice. The wait time is the amount of time that elapses from when cat X finishes eating, and then cat X starts to eat again. Assume fairness amongst the animals of the same type: once cat X eats, all other cats will eat exactly once before cat X eats again.

```
b                        c                        m                        t                        k
10                       5                        5                        1                        5
1/2                      1                        1                        1/2                    1
1                        10                       10                       5                       1
10                       10                       5                        1                        5
1/2                      1                        3                        1                        1
1                        10                       5                        1                        1
10                       50                       25                       5                       25
5/6                      55                       25                       10                      25
10                       11                       9                        10                      10
2/3                      50                       20                       0                       0
```

```json
{
  "problem_id": "4-c",
  "points": 4,
  "type": "Freeform",
  "tags": ["cat-mouse", "concurrency", "analysis"],
  "answer": "See the provided scenarios table. For each row compute: efficiency = (number of animals eating concurrently) / b (cap at 1), and maximum wait time for a cat = (number of cat groups served before it can eat again) * average eating time t, similarly for mice. Exact numeric answers depend on applying the k-window serving policy to each row.",
  "llm_judge_instructions": "Award 4 points for correctly computing efficiency and maximum wait times for all rows. Suggested rubric: 2 points for correct efficiency computations across rows, 2 points for correct maximum wait time calculations for both cats and mice across rows. Partial credit for partially correct rows."
}
```

---

## Question 5 [9 Points]

For this problem, you are required to use semaphores to simulate a school cafeteria.

- There are an arbitrary number of students. Each student is a separate thread. 
- There are only student threads. There is no “coordinating” or “dispatching” thread. 
- There is an arbitrary number of student threads. 
- There are K stations in the cafeteria, numbered 0..K-1 (where K is a global constant) 
- Only one student can occupy a station at a time. 
- Students may not cut in line or skip a station.  They must maintain their original ordering (sequence) and must start at station 0 and finish at station K-1. 
- There may be more students than stations, so you must also maintain a queue of students waiting to get to the first station. The following unsynchronized list functions (similar to the linked lists shown in class) should be sufficient. 
  int is_empty(); 
  struct student *list_peek_front(); 
  struct student *list_remove_front(); 
  void list_append(struct student *s); 
- Each student may need more than one food “item” at a station. The number of items student s needs to acquire at station i is s->items[i], which could be zero. 
- For each item at station i the student must call: get_item(struct student *s, int i); When the function returns, the student will have the item, but it may block during the function call to wait for the food. 
- You must ensure that get_item is synchronized and is never called more than once at the same time for either the same student s or the same station i. 
- You may use thread_sleep and thread_wakeup if you wish. 
List your global variables and semaphores here. Indicate the initial value of each variable & semaphore.

```json
{
  "problem_id": "5",
  "points": 9,
  "type": "Freeform",
  "tags": ["semaphores", "synchronization", "cs530"],
  "answer": "Suggested global variables and semaphores:\n\n1) struct semaphore *queue_lock; // protects access to the waiting queue and list operations. Initial value = 1.\n2) struct semaphore *station_lock[K]; // one semaphore per station to ensure only one student occupies a station at a time. Each initialized to 1.\n3) struct semaphore *get_item_lock[K]; // one semaphore per station to serialize get_item calls for that station. Initial value = 1. (Alternatively, reuse station_lock if get_item must be exclusive with station occupancy.)\n4) For per-student mutual exclusion on get_item(s, i), include a per-student semaphore: struct semaphore *student_lock[N] or a mutex inside the student struct; initial value = 1. If N (number of students) is dynamic, create the semaphore when the student thread is created.\n5) Optionally, a counting semaphore stations_available (initial value = K) to gate entry into the first station area.\n\nSynchronization guarantees: use queue_lock to append/remove from the queue and to ensure FIFO ordering for entering station 0. A student waiting for station i should acquire station_lock[i] before moving into the station, and release it after finishing all items at that station. Acquire per-student lock before calling get_item(s,i) to prevent concurrent get_item calls for the same student; acquire get_item_lock[i] (or station_lock[i]) to prevent concurrent get_item calls for the same station. Ensure all semaphores are binary (1) where mutual exclusion is required. This design meets the requirement that get_item is never called concurrently for the same student or the same station.",
  "llm_judge_instructions": "Award points as follows: 3 points for correctly listing and initializing synchronization primitives for queue protection (e.g., queue_lock) and explaining FIFO queue protection; 3 points for correctly listing per-station semaphores (station_lock and/or get_item_lock) with initial values and explaining how they ensure exclusive station occupancy and serialized get_item calls per station; 2 points for describing per-student mutual exclusion (per-student lock) to prevent concurrent get_item calls by the same student; 1 point for any additional correct detail (e.g., stations_available semaphore or dynamic initialization). Total 9 points."
}
```

---

*** END OF EXAM ***