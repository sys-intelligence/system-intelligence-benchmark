[PROMPT]
Provide complete `free_dirs.c` file that implement `free_dirs` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[GUARANTEE]
```c
void free_dirs(char *dirname[]);
```

[SPECIFICATION]
**Pre-Condition**:
  * `dirname` is a pointer to a `NULL`-terminated array of character pointers (strings).
  * Each non-`NULL` element in the `dirname` array points to a valid block of dynamically allocated memory that can be safely passed to `free()`.

**Post-Condition**:
  * The memory pointed to by each non-`NULL` element in the `dirname` array is deallocated.
  * The pointer to the `dirname` array itself is **not** freed.


**System Algorithm**:
  * The function should iterate through the `dirname` array until it encounters a `NULL` terminator. For each string it encounters, it should call `free()` to release its memory.
