[PROMPT]
Provide complete `calculate.c` file that implement `calculate` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
char** malloc_path(unsigned len);
```
```c
char* malloc_string(const char* name);
```

[GUARANTEE]
```c
char** calculate(char* srcpath[], char* dstpath[]);
```

[SPECIFICATION]
**Pre-Condition**:
- `srcpath` and `dstpath` are valid NULL-terminated arrays of strings (non-NULL pointers).
- Each array element is a non-NULL string pointer until the final NULL terminator.
- The functions `malloc_path` and `malloc_string` behave as described (allocate memory and return valid pointers).
**Post-Condition**:
Returns a NULL-terminated array `compath` containing the **longest common prefix** of `srcpath` and `dstpath`. 

