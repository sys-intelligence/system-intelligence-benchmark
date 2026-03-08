[PROMPT]
Provide complete `atomfs_read.c` file that implement `atomfs_read` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

## First Prompt
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
extern struct inode *root_inum;
```
```c
typedef struct read_ret {
	char *buf;
	unsigned num;
} read_ret;
```
// Traverse path under cur. If an inode is found, the return value is the found inode. If no inode is found, the return value is NULL. The lock of cur is released before returning, and the lock of the found inode is acquired.
```c
struct inode* locate(struct inode* cur, char* path[]);
```
```c
int check_file(struct inode *inum);
```
```c
struct read_ret* inode_read(struct inode* node, unsigned len, unsigned offset);
```

[GUARANTEE]
```c
struct read_ret* atomfs_read(char* path[], unsigned size, unsigned offset);
```

[SPECIFICATION]
**Pre-Condition**:
`root_inum` is a valid directory inode. The `path` corresponds to an existing entry in the file system hierarchy rooted at `root_inum`, ensuring `locate(root_inum, path)` returns a valid non-NULL inode.
**Post-Condition**:
The return value depends on the validity of the located inode and the read operation:

**Case 1**: Starting from `root_inum`, by following the `path`, find the `inum`. If `check_file(inum)` indicates the inode is not readable (returns `1`), the function returns `NULL`.

**Case 2**: Otherwise, the function reads `size` bytes from `buf` at `offset` into the file via `inode_read` and returns the result of `inode_read`. 



## Refine Prompt
[RELY]
```c
void lock(struct inode* inum);
```
```c
void unlock(struct inode* inum);
```

[SPECIFICATION of locate]
**Pre-Condition**:
cur is locked.
**Post-Condition**:
If target is NULL, locate would have released all locks, so no lock is owned in this case.
If target is not NULL, only the lock of target is owned. locate would have released all other locks.


[SPECIFICATION of atomfs_read]
**Pre-Condition**:
no lock is owned. You should first acquire the lock of root_inum.
**Post-Condition**:
no lock is owned.


[SPECIFICATION of check_file]
**Pre-Condition**:
If `inum` is not NULL, it is locked.
**Post-Condition**:
Failure, return 1:
`inum` is NULL or `1num` is a directory, the lock is released and returned.
Success, return 0:
`inum` is still locked.


