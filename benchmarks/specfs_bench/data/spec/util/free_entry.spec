[PROMPT]
Provide complete `free_entry.c` file that implement `free_entry` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
void free_entry(struct entry* en);
```

[SPECIFICATION]
**Pre-Condition**:
- `en` points to a valid entry structure.
**Post-Condition**:
- The function frees the name of the entry and the entry structure itself.

