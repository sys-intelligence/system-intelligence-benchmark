[PROMPT]
Provide complete `inode_truncate.c` file that implement `inode_truncate` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `inode.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
void file_clear(struct inode *node, unsigned start, unsigned len);
```
```c
void file_allocate(struct inode *node, unsigned offset, unsigned len);
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
void inode_truncate(struct inode* node, unsigned size);
```

[SPECIFICATION]
**Pre-Condition**:
- `node` points to a valid inode structure with initialized `size` and `file` fields. the `file` field of the inode points to a valid `indextb` structure with `size` bytes allocated (non-NULL).
- `size` is a non-negative integer.
**Post-Condition**:
- Case 1: If `size` is less than the current size of the inode, the file is truncated to `size` bytes. The remaining bytes are cleared.
- Case 2: If `size` is greater than or equal to the current size, allocate additional space in the file and clear the newly allocated space.


