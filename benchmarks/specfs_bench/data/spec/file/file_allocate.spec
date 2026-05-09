[PROMPT]
Provide complete `file_allocate.c` file that implement `file_allocate` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `file.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
unsigned char* malloc_page();
```
```c
typedef struct indextb {
	unsigned char *index[INDEXTB_NUM];
} indextb;
```
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
void file_allocate(struct inode *node, unsigned offset, unsigned len);
```

[SPECIFICATION]
**Pre-Condition**:
- The `node` parameter points to a valid `inode` structure, i.e., `tb` is not NULL. The index_num is guarenteed to be within bounds.
- The `offset` is the offset in the file where the allocation starts.
- The `len` is the number of bytes to allocate starting from the `offset`.
**Post-Condition**:
- Calculate the starting page and the end page, each page is of `PG_SIZE` bytes.
- Iterate from the starting page to the end page, allocating pages as needed.

