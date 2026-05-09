[PROMPT]
Provide complete `malloc_entry.c` file that implement `malloc_entry` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
typedef struct entry {
	char *name;
	void *inum;
	struct entry *next;
} entry;
```

[GUARANTEE]
```c
struct entry *malloc_entry();
```

[SPECIFICATION]
**Pre-Condition**:
None.
**Post-Condition**:
  - **Case 1 (Successful allocation)**:
      - Returns a valid pointer to a newly allocated memory block of size `sizeof(struct entry)`.
      - The content of the allocated memory is uninitialized.
  - **Case 2 (Allocation failure)**:
      - Returns `NULL`.

