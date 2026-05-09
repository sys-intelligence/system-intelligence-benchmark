[PROMPT]
Provide complete `inode_read.c` file that implement `inode_read` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `inode.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
void file_read(struct inode *node, unsigned offset, unsigned len, char *data);
```
```c
struct read_ret* malloc_readret();
```
```c
char* malloc_buffer(unsigned len);
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
```c
typedef struct read_ret {
	char *buf;
	unsigned num;
} read_ret;
```

[GUARANTEE]
```c
struct read_ret* inode_read(struct inode* node, unsigned len, unsigned offset);
```

[SPECIFICATION]
**Pre-Condition**:
- `node` points to a valid inode structure with initialized `size` and `file` fields. the `file` field of the inode points to a valid `indextb` structure with `size` bytes allocated (non-NULL).
**Post-Condition**:
The function returns a non-NULL pointer to a dynamically allocated `read_ret` structure. Two cases define the outcome:

**Case 1**: The read range is empty (`offset ≥ node->size` or `len == 0`).

- `ret->num` = `0`.
- `ret->buf` is  `NULL`

**Case 2**: Data is read (`offset < node->size` and `len > 0`).

- `ret->num` = `min(len, node->size - offset)` (actual bytes read).
- `ret->buf` points to a buffer containing `ret->num` bytes copied from the file starting at `offset`.

**System Algorithm**:
*The caller is responsible for freeing `ret->buf` (if non-`NULL`) and the `read_ret` structure.*
