# CS 423 Operating Systems Design Fall 2025 Final

```json
{
  "exam_id": "cs_423_operating_systems_design_fall_2025_final",
  "test_paper_name": "CS 423 Operating Systems Design Fall 2025 Final",
  "course": "CS 423",
  "institution": "UIUC",
  "year": 2025,
  "score_total": 24,
  "score_max": 21.5,
  "score_avg": 12.88,
  "score_median": 14.5,
  "score_standard_deviation": 6.25,
  "num_questions": 18
}
```

---

## Question 1 [2 points]

Applications in a VM should see no difference from running on a physical machine. An application calls `open()`.

Describe how this system call is handled in a virtualized environment. What does the host OS / VMM do, and how do the host and guest OS cooperate? (2 points)

```json
{
  "problem_id": "1",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtualization"],
  "answer": "The system call traps into the guest OS; the VMM calls the guest OS handler with reduced privilege. The guest OS executes the syscall handler and returns to th VMM. The VMM completes the trap return and resumes guest execution.",
  "llm_judge_instructions": "When guest OS installs the handler, the VMM should know, and it will call the guest OS handler with reduced privilege. Grade by understanding."
}
```

---

## Question 2 [2 points]

Modern CPUs support nested (2D) page-table walks. A 4-level radix tree costs 24 steps in the worst case.

If both the guest and host use 5-level page tables, how many steps does nested translation take in the worst case? (2 points)

```json
{
  "problem_id": "2",
  "points": 2,
  "type": "Freeform",
  "tags": ["virtualization", "address-translation", "page-tables"],
  "answer": "35 steps.",
  "llm_judge_instructions": "There are 6*5+5 steps. Answer must match."
}
```

---

## Question 3 [1 point]

Can you describe the difference in handling page faults in a bare-metal (non-virtualized) environment versus a virtualized environment (e.g., in the guest)? (1 point)

```json
{
  "problem_id": "3",
  "points": 1,
  "type": "Freeform",
  "tags": ["virtualization", "page-faults"],
  "answer": "Assume EPT. It may involve VM exit. When there does not exist GPA->HPA, there will be a VM exit, and the hypervisor needs to allocate a new page for the guest machine.",
  "llm_judge_instructions": "Must mention possible hypervisor involvement via VM exit. Grade by understanding."
}
```

---

## Question 4 [1 point]

We also discussed hashed page table design in the class. Assume we have a magic hash function to use – e.g., hash collisions will never happen. With this magic hash function, how many steps will it take for nested translation using a hashed page table design? (1 point)

```json
{
  "problem_id": "4",
  "points": 1,
  "type": "Freeform",
  "tags": ["virtualization", "page-tables"],
  "answer": "Two steps or one step.",
  "llm_judge_instructions": "Two steps for EPT-style translation, or one step if using a shadow page table style translation. Grade by understanding, there are also other possible answers."
}
```

---

## Question 5 [1 point]

Peizhe presented a software based technique to accelerate memory translation, called HugeGPT (nothing to do with ChatGPT) – the idea is to allocate guest pages using huge pages in the host. Tianyin is not satisfied and asks Peizhe to continue optimizing the performance. Can you help Peizhe? Please write an idea for minimizing memory virtualization overhead that only requires software changes. (Life is too short to wait for future hardware) (1 point)

```json
{
  "problem_id": "5",
  "points": 1,
  "type": "Freeform",
  "tags": ["virtualization", "performance"],
  "answer": "Example answer: profile hot VMAs and build a shadow page table only for those regions, reducing page-walk overhead without frequent VM exits.",
  "llm_judge_instructions": "Any reasonable software-only optimization idea that reduces translation overhead is acceptable."
}
```

---

## Question 6 [1 point]

What does `fsync()` do?

```json
{
  "problem_id": "6",
  "points": 1,
  "type": "Freeform",
  "tags": ["file-systems", "durability"],
  "answer": "It ensures that all dirty data and required metadata for the file descriptor are persisted.",
  "llm_judge_instructions": "Must mention both dirty data and metadata. Grade by understanding."
}
```

---

## Question 7 [1 point]

Can you write how fsync() is implemented? We are not expecting you to have read the kernel source code of the fsync implementation. Instead, we want you to reason about what operations should be done by fsync If you were to do it. (1 point)

```json
{
  "problem_id": "7",
  "points": 1,
  "type": "Freeform",
  "tags": ["file-systems", "durability"],
  "answer": "1. Gather dirty data page and metadata associated with the fd. 2. Issue a write to storage and update the metadata. 3. Commit the journal (depends on the FS).",
  "llm_judge_instructions": "Must mention both dirty data and metadata. Grade by understanding."
}
```

---

## Question 8 [2 points]

We discussed inodes as a key data structure for file systems. In a filesystem F423, an inode has:

(a) 12 direct pointers

(b) 1 single-indirect pointer

(c) 1 double-indirect pointer

Assume that a disk block is 4KB (same as the page size) and a pointer is 4 bytes.

What is the maximum file size supported by F423? (2 points)

```json
{
  "problem_id": "8",
  "points": 2,
  "type": "Freeform",
  "tags": ["file-systems", "inodes"],
  "answer": "48KB (direct) + 4MB (single-indirect) + 4GB (double-indirect) = 48KB + 4MB + 4GB.",
  "llm_judge_instructions": "Direct: 12*4KB; single-indirect: 1024*4KB; double-indirect: 1024*1024*4KB. Answer must match (can use different expression/units)."
}
```

---

## Question 9 [1 point]

Consider that when we create a file, we have the following operations:

(a) Add the file name and an empty inode pointer in the directory

(b) Create a new inode of the file

(c) Update the empty pointer to the actual pointer of the created inode

Do you think the above operation sequence is crash-safe? If not, what is the right Sequence? (1 point)

```json
{
  "problem_id": "9",
  "points": 1,
  "type": "Freeform",
  "tags": ["file-systems", "crash-consistency"],
  "answer": "Not crash-safe. The correct ordering is b,a,c.",
  "llm_judge_instructions": "The inode pointer can be dangling. The answer must match."
}
```

---

## Question 10 [2 points]

In MP-2, we have implemented a Rate Monotonic Scheduler (RMS), where each task is modeled by its period and computation time, and have three states: Sleeping, Ready, and Running (the full MP documentation is presented in the reference materials).

In MP-2, we used kmem_cache instead of the traditional kmalloc. Name one advantage and one limitation of kmem_cache. (2 points)

```json
{
  "problem_id": "10",
  "points": 2,
  "type": "Freeform",
  "tags": ["realtime-scheduling", "linux-kernel"],
  "reference_materials": ["MP2.md"],
  "answer": "Advantage: faster allocation and reuse for same-sized objects via slab caching. Limitation: fixed-size objects and additional setup/management overhead.",
  "llm_judge_instructions": "Must include one advantage and one disadvantage. There can be other answers. Grade by understanding."
}
```

---

## Question 11 [1 point]

In MP-2, we have implemented a Rate Monotonic Scheduler (RMS), where each task is modeled by its period and computation time, and have three states: Sleeping, Ready, and Running (the full MP documentation is presented in the reference materials).

A security camera system uses our MP-2 scheduler. There are many security cameras, and they all register themselves as independent processes. However, one camera in the system behaves abnormally, and is stuck at the Running state. We assume that the system is uniprocessor in the following questions.

In this case, what will happen to other security cameras? (1 point)

```json
{
  "problem_id": "11",
  "points": 1,
  "type": "Freeform",
  "tags": ["realtime-scheduling", "linux-kernel"],
  "reference_materials": ["MP2.md"],
  "answer": "They will get stuck, as one camera keeps running and never yields, and all cameras have same period, the dispatcher finds nothing to schedule for the next.",
  "llm_judge_instructions": "Must mention they are stuck. Grade by understanding."
}
```

---

## Question 12 [2 points]

In MP-2, we have implemented a Rate Monotonic Scheduler (RMS), where each task is modeled by its period and computation time, and have three states: Sleeping, Ready, and Running (the full MP documentation is presented in the reference materials).

MP-2 is built on and works with the existing Linux scheduler.

A security camera system uses our MP-2 scheduler. There are many security cameras, and they all register themselves as independent processes. However, one camera in the system behaves abnormally, and is stuck at the Running state. We assume that the system is uniprocessor in the following questions.

What will happen to the whole OS, and why? You need to explain at the scheduler level. Only mentioning “something is different” is not sufficient, you need to explain why such difference has caused the issue. (2 points)

```json
{
  "problem_id": "12",
  "points": 2,
  "type": "Freeform",
  "tags": ["realtime-scheduling", "linux-kernel"],
  "reference_materials": ["MP2.md"],
  "answer": "MP-2 task runs at SCHED_FIFO RT scheduler. They have higher priority than CFS processes. If it got stuck, it will prevent CFS processes from being scheduled normally. System will throttle, but NOT stall/crash, as RT can be throttled.",
  "llm_judge_instructions": "Must mention MP-2 uses SCHED_FIFO RT policy and it has priority over CFS. Must mention system will throttle. Grade by understanding."
}
```

---

## Question 13 [1 point]

In MP-3, we have implemented a lightweight tool that can profile the page fault rate and organize them in a shared memory buffer. With the tool, we also performed two case studies, to observe the page fault rate and CPU utilization (the full MP documentation is presented in the reference materials).

In MP-3, we used vmalloc instead of the traditional kmalloc. Why? (1 point)

```json
{
  "problem_id": "13",
  "points": 1,
  "type": "Freeform",
  "tags": ["linux-kernel", "virtual-memory"],
  "reference_materials": ["MP3.md"],
  "answer": "Because we have a large buffer. Kmalloc allocs physically contiguous memory, which can be difficult to alloc such a big buffer. Vmalloc does not require this.",
  "llm_judge_instructions": "Must mention large buffer and kmalloc's limitation. Grade by understanding."
}
```

---

## Question 14 [1 point]

In MP-3, we have implemented a lightweight tool that can profile the page fault rate and organize them in a shared memory buffer. With the tool, we also performed two case studies, to observe the page fault rate and CPU utilization (the full MP documentation is presented in the reference materials).

Remember that from the Case Study 2, CPU utilization dropped significantly after a certain degree of multiprogramming. Please explain the reason. Only mentioning the terminology is not sufficient, you need to explain it. (1 point)

```json
{
  "problem_id": "14",
  "points": 1,
  "type": "Freeform",
  "tags": ["virtual-memory", "performance"],
  "reference_materials": ["MP3.md"],
  "answer": "They suffer from page thrashing. When physical memory is overcommitted, swap (which is extremely slow due to io) happens frequently and reduces utilization.",
  "llm_judge_instructions": "Must explain swapping/IO, not just name thrashing. Grade by understanding."
}
```

---

## Question 15 [1 point]

In MP-3, we have implemented a lightweight tool that can profile the page fault rate and organize them in a shared memory buffer. With the tool, we also performed two case studies, to observe the page fault rate and CPU utilization (the full MP documentation is presented in the reference materials).

Remember that we set the reserved bit for all pages in the shared buffer. Give one potential issue if we did not do so. (1 point)

```json
{
  "problem_id": "15",
  "points": 1,
  "type": "Freeform",
  "tags": ["virtual-memory", "linux-kernel"],
  "reference_materials": ["MP3.md"],
  "answer": "We set the reserved bit because we want to prevent it from swapping. If we do not set, it can be swapped to disk, and thus slowing down our buffer.",
  "llm_judge_instructions": "Must mention prevention of swapping. Grade by understanding"
}
```

---

## Question 16 [2 points]

In MP-3, we have implemented a lightweight tool that can profile the page fault rate and organize them in a shared memory buffer. With the tool, we also performed two case studies, to observe the page fault rate and CPU utilization (the full MP documentation is presented in the reference materials).

Peizhe felt this MP is much easier than the previous one, as he could finish it fairly quickly. Obviously, he wrote buggy code. Shown below is his mmap handler for the character device:

```c
static int cdev_mmap(struct file *file, struct vm_area_struct *vma)
{
   unsigned long pfn;
   unsigned long size = vma->vm_end - vma->vm_start;
   unsigned long offset = vma->vm_pgoff << PAGE_SHIFT;
   unsigned long kbuf_addr = (unsigned long)kbuf + offset;

   if (size > BUFFER_SIZE) {
       pr_err("mmap size exceeds buffer size\n");
       return -EINVAL;
   }

   pfn = vmalloc_to_pfn((void *)kbuf_addr);
   if (remap_pfn_range(vma, vma->vm_start, pfn, size, vma->vm_page_prot)) {
       pr_err("remap_pfn_range failed\n");
       return -EAGAIN;
   }

   return 0;
}
```

Please help Peizhe to identify the problem, and explain. (2 points)

```json
{
  "problem_id": "16",
  "points": 2,
  "type": "Freeform",
  "tags": ["linux-kernel", "mmap", "virtual-memory"],
  "reference_materials": ["MP3.md"],
  "answer": "Vmalloc memory is not physically contiguous. Thus, we cannot use PFN range to remap the whole buffer at once. We need to do it page by page (PFN by PFN) by introducing a loop.",
  "llm_judge_instructions": "Must find the exact issue. Grade by understanding."
}
```

---

## Question 17 [1 point]

In MP4, we implemented a Rex kernel extension program that reads and pass CPU time for registered pids between kernel and userspace using Rust language (the full MP documentation is presented in the reference materials).

eBPF only provides spin lock as synchronization primitive and programs are triggered by hooks. Could you explain why mutex locks are disallowed? (1 point)

```json
{
  "problem_id": "17",
  "points": 1,
  "type": "Freeform",
  "tags": ["ebpf", "synchronization", "linux-kernel"],
  "reference_materials": ["MP4.md"],
  "answer": "Because eBPF programs may run in atomic or non-sleepable contexts; mutexes can sleep and are unsafe/unverifiable in such contexts.",
  "llm_judge_instructions": "Grade by understanding."
}
```

---

## Question 18 [1 point]

In MP4, we implemented a Rex kernel extension program that reads and pass CPU time for registered pids between kernel and userspace using Rust language (the full MP documentation is presented in the reference materials).

Rust's unwrap() just bombed Cloudflare's infrastructure, and some students' incorrect implementations also crashed their kernels. Can you use unwrap() in your Rex kernel extension? Please explain why. (1 point)

```json
{
  "problem_id": "18",
  "points": 1,
  "type": "Freeform",
  "tags": ["rust", "linux-kernel"],
  "reference_materials": ["MP4.md"],
  "answer": "Yes. unwrap() can be called because panic will be captured in Rex.",
  "llm_judge_instructions": "Grade by understanding."
}
```
