[PROMPT]
Provide complete `free_readret.c` file that implement `free_readret` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
typedef struct read_ret {
	char *buf;
	unsigned num;
} read_ret;
```

[GUARANTEE]
```c
void free_readret(struct read_ret *p);
```

[SPECIFICATION]
**Pre-Condition**:
  - `p` points to a valid `read_ret` structure.
  - `p->buf` points to a dynamically allocated buffer.
**Post-Condition**:
  - The function frees the memory allocated for the buffer (`p->buf`) and the `read_ret` structure (`p`) itself.

