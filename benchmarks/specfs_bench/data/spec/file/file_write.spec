[PROMPT]
Provide complete `file_write.c` file that implement `file_write` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `file.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
```c
typedef struct indextb {
	unsigned char *index[INDEXTB_NUM];
} indextb;
```
```c
typedef struct inode {
	int mutex;
	struct mcs_mutex *impl;
	struct mcs_node *hd;
	unsigned maj;
	unsigned min;
	unsigned int mode;
	unsigned int size;
	struct dirtb *dir;
	struct indextb *file;
} inode;
```

[GUARANTEE]
```c
void file_write(struct inode *node, unsigned offset, unsigned len, const char *data);
```

[SPECIFICATION]
**Pre-Condition**:
- `node` is a valid `inode` structure, and its `tb` is a valid pointer, `tb->index` array is sufficiently large to hold all page numbers required for the range [`offset`, `offset + len`). 
- `offset` and `len` are valid unsigned integers, and `offset + len` does not cause an overflow. 
- If `data` is not `NULL`, it points to a buffer of at least `len` bytes, and all required pages (derived from the range [`offset`, `offset + len`)) in `tb->index` are already allocated (non-`NULL`).

**Post-Condition**:
The specified range [`offset`, `offset + len`) is processed as follows:

**Case 1**: `data` is `NULL`  
- All bytes in the range are initialized to zero. For any page in the range that was unallocated (`tb->index[page]` was `NULL`), the page is allocated, and the relevant portion within the range is zero-initialized. Pages are left unmodified outside the specified range.

**Case 2**: `data` is not `NULL`  
- The `len` bytes from the `data` buffer are copied into the corresponding positions within the allocated pages of `tb`. All pages in the range are assumed pre-allocated (as per the precondition), and the data is fully written. 

In both cases, the entire `len` bytes are processed, and variables `current_offset` and `remaining` reflect completion (e.g., `remaining == 0`).

