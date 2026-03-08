[PROMPT]
Provide complete `file_read.c` file that implement `file_read` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `file.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
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
void file_read(struct inode *node, unsigned offset, unsigned len, char *data);
```

[SPECIFICATION]
**Pre-Condition**:
- The `node` parameter points to a valid `inode` structure, i.e., `tb` is not NULL.
- The requested read range is fully allocated, meaning for every index `i` in the range from `offset >> 12` (inclusive) to the index of the last byte of the read (inclusive), `tb->index[i]` must be non-NULL and point to a valid memory block of size PG_SIZE (4096 bytes).
- The buffer `data` has `len` bytes allocated.
**Post-Condition**:
- The buffer `data` contains the exact `len` bytes from the specified offset. For any valid index i, `tb->index[i]` contains bytes range [i*PG_SIZE+1, (i+1) * PG_SIZE].

