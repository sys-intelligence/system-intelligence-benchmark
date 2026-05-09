[PROMPT]
Provide complete `getlen.c` file that implement `getlen` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[GUARANTEE]
```c
int getlen(char* path[]);
```

[SPECIFICATION]
**Pre-Condition**:
- `path` is a valid **NULL-terminated array** of strings
**Post-Condition**:
Returns the **number of non-NULL elements** in `path` before the terminating `NULL`

