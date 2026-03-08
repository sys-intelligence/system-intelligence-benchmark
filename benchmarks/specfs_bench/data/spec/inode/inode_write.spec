[PROMPT]
Provide complete `inode_write.c` file that implement `inode_write` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `inode.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
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
void file_allocate(struct inode *node, unsigned offset, unsigned len);
```
```c
void file_clear(struct inode *node, unsigned start, unsigned len);
```
// `file_write` writes a given data buffer (or zeroes if `data` is `NULL`) into a file’s page-indexed storage, handling offsets, page boundaries, and partial writes until the specified length is covered.
```c
void file_write(struct inode *node, unsigned offset, unsigned len, const char *data);
```

[GUARANTEE]
```c
unsigned inode_write(struct inode* node, const char* buffer, unsigned len, unsigned offset);
```

[SPECIFICATION]
**Pre-Condition**:
- `node` points to a valid inode structure with initialized `size` and `file` fields. the `file` field of the inode points to a valid `indextb` structure with `size` bytes allocated (non-NULL).
- `buffer` is a valid pointer to a buffer containing data to write.
- `len` is a non-negative integer representing the number of bytes to write.
- `offset` is a non-negative integer representing the position in the file to write the data.
**Post-Condition**:
- Calculate the new size of the file after the write operation. If the new size exceeds the maximum file size, truncate it to `MAX_FILE_SIZE`.
- If the new size is greater than the current size, allocate additional space in the file, clear the newly allocated space, and set the node's size to the new size.
- Write the data from `buffer` to the file at the specified `offset` and return the number of bytes written.
