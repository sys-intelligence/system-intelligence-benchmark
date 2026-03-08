[PROMPT]
Provide complete `malloc_string.c` file that implement `malloc_string` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[GUARANTEE]
```c
char* malloc_string(const char* name);
```

[SPECIFICATION]
**Pre-Condition**:
- `name` is a non-NULL pointer
**Post-Condition**:
- Returns a pointer to newly allocated memory containing an exact copy of `name`, including the null terminator.
- The returned pointer is always non-NULL (assumes `malloc` succeeds).

