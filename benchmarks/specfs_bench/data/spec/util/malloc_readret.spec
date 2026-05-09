[PROMPT]
Provide complete `malloc_readret.c` file that implement `malloc_readret` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
typedef struct read_ret {
	char *buf;
	unsigned num;
} read_ret;
```

[GUARANTEE]
```c
struct read_ret* malloc_readret();
```

[SPECIFICATION]
**Pre-Condition**:
There is sufficient memory available to allocate a struct read_ret.
**Post-Condition**:
The function returns a pointer to a newly allocated struct read_ret instance. The buf field is initialized to a null pointer (0), and the num field is initialized to 0. The returned pointer is properly aligned for accessing a struct read_ret object. If memory allocation fails, the function returns NULL.


