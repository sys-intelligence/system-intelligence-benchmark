[PROMPT]
Provide complete `malloc_page.c` file that implement `malloc_page` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
#define PG_SIZE 4096
#define INDEXTB_NUM 8192
#define DIRTB_NUM 512
#define MAX_FILE_LEN 256
#define MAX_DIR_SIZE 10000000
#define MAX_PATH_LEN 100
#define MAX_FILE_SIZE ((unsigned)(INDEXTB_NUM * PG_SIZE))
#define PAGE_SIZE (4096)
```

[GUARANTEE]
```c
unsigned char* malloc_page();
```

[SPECIFICATION]
**Pre-Condition**:
None.
**Post-Condition**:
- Allocates a new page of memory and returns a pointer to it.
- The allocated memory should be zero-initialized.

