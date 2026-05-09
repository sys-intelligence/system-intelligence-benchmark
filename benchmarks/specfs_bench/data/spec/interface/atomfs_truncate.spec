[PROMPT]
Provide complete `atomfs_truncate.c` file that implement `atomfs_truncate` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

## First Prompt
[RELY]
```c
int check_file(struct inode *inum);
```
```c
void inode_truncate(struct inode* node, unsigned size);
```
// Traverse path under cur. If an inode is found, the return value is the found inode. If no inode is found, the return value is NULL. The lock of cur is released before returning, and the lock of the found inode is acquired.
```c
struct inode* locate(struct inode* cur, char* path[]);
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
```c
extern struct inode *root_inum;
```

[GUARANTEE]
```c
int atomfs_truncate(char* path[], unsigned offset);
```

[SPECIFICATION]
**Pre-Condition**:
  * `path` must be a valid NULL-terminated array of strings representing the file path.
  * `offset` is the target size for truncation.
**Post-Condition**:
**Case 1 (Successful truncation)**:

  * The file identified by `path` is truncated to `offset` bytes.
  * Returns `0` to indicate success.

**Case 2 (Failure)**:

  * The file system state remains unchanged.
  * Returns `-1` if any of the following occur:
    a) The `offset` is greater than `MAX_FILE_SIZE`.
    b) The path traversal fails (starting from `root_inum`, following the `path` via `locate` but returns NULL).
    c) The target inode is not a regular file (`check_file` returns non-zero).


**Invariant**: 
**Well-formedness of root_inum**: The global `root_inum` must point to a valid, initialized directory inode.

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
`cur` is locked.
**Post-Condition**:
If `locate` returns a non-NULL `target` inode, only the lock of `target` is owned. If `locate` returns NULL, no lock is owned.


[SPECIFICATION of check_file]
**Pre-Condition**:
`inum` is locked.
**Post-Condition**:
If `check_file` returns 0 (success), `inum` remains locked. If `check_file` returns 1 (failure), the lock on `inum` is released.


[SPECIFICATION of inode_truncate]
**Pre-Condition**:
`inum` is locked.
**Post-Condition**:
`inum` remains locked.


[SPECIFICATION of atomfs_truncate]
**Pre-Condition**:
No lock is owned.
**Post-Condition**:
No lock is owned.


