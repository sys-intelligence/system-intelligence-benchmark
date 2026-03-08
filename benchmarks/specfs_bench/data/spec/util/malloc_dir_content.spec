[PROMPT]
Provide complete `malloc_dir_content.c` file that implement `malloc_dir_content` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
//  The standard C library function `malloc` for dynamic memory allocation
extern void *malloc(size_t __size)
```

[GUARANTEE]
```c
char** malloc_dir_content(unsigned size);
```

[SPECIFICATION]
**Pre-Condition**:
  - `size` is an unsigned integer representing the number of character pointers to allocate.
**Post-Condition**:
  - **Case 1: Successful Allocation**
      - Returns a pointer (`char**`) to a newly allocated block of memory.
      - The allocated memory is large enough to hold an array of `size` elements, where each element is a pointer to a character (`char*`).
      - The allocated memory is not initialized.
  - **Case 2: Allocation Failure**
      - Returns `NULL` if the memory allocation fails.

