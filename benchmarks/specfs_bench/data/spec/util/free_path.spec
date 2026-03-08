[PROMPT]
Provide complete `free_path.c` file that implement `free_path` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[GUARANTEE]
```c
void free_path(char** path);
```

[SPECIFICATION]
**Pre-Condition**:
- `path` is a pointer to a **NULL-terminated array of strings** (last element is `NULL`).
**Post-Condition**:
- All strings in the array (`path[0]`, `path[1]`, etc.) are deallocated using `free()`.
- The array itself (`path`) is deallocated using `free()`.

