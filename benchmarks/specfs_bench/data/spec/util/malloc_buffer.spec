[PROMPT]
Provide complete `malloc_buffer.c` file that implement `malloc_buffer` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[GUARANTEE]
```c
char* malloc_buffer(unsigned len);
```

[SPECIFICATION]
**Pre-Condition**:
There is enough memory to allocate a buffer of length `len`.
**Post-Condition**:
Allocate a buffer of length `len` and return a pointer to the buffer.

