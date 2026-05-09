[PROMPT]
Provide complete `file_clear.c` file that implement `file_clear` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `file.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
// `file_write` writes a given data buffer (or zeroes if `data` is `NULL`) into a file’s page-indexed storage, handling offsets, page boundaries, and partial writes until the specified length is covered.
```c
void file_write(struct inode *node, unsigned offset, unsigned len, const char *data);
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
void file_clear(struct inode *node, unsigned start, unsigned len);
```

[SPECIFICATION]
**Pre-Condition**:
- The `node` parameter points to a valid `inode` structure, i.e., `node` is not NULL.
- The `start` is the starting offset in the file where the clear operation begins.
- The `len` is the number of bytes to clear starting from the `start` offset.

**Post-Condition**:
- The specified range in the file is cleared (set to zero).

