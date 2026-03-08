[PROMPT]
Provide complete `atomfs_getattr.c` file that implement `atomfs_getattr` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

## First Prompt
[RELY]
// Traverse path under cur. If an inode is found, the return value is the found inode. If no inode is found, the return value is NULL. The lock of cur is released before returning, and the lock of the found inode is acquired.
```c
struct inode* locate(struct inode* cur, char* path[]);
```
```c
struct getattr_ret* malloc_getattr_ret(struct inode* inum, unsigned mode, unsigned size, unsigned maj, unsigned min);
```
```c
typedef struct getattr_ret {
	struct inode *inum;
	unsigned mode;
	unsigned size;
	unsigned maj;
	unsigned min;
} getattr_ret;
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
struct getattr_ret* atomfs_getattr(char* path[]);
```

[SPECIFICATION]
**Pre-Condition**:
  * `path` must be a valid NULL-terminated array of strings representing the path to the target inode.
**Post-Condition**:
**Case 1 (Successful lookup)**:

  * Starting from `root_inum`, the path is successfully traversed to find the target inode.
  * A new `getattr_ret` structure is allocated and populated with the attributes (`mode`, `size`, `maj`, `min`) of the found inode.
  * Returns a pointer to the newly allocated `getattr_ret` structure.

**Case 2 (Lookup failure)**:

  * Returns `NULL` if the path traversal fails (`locate` returns NULL).

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
If `target` is NULL, `locate` would have released all locks, so no lock is owned in this case.
If `target` is not NULL, only the lock of `target` is owned. `locate` would have released all other locks.


[SPECIFICATION of atomfs_getattr]
**Pre-Condition**:
no lock is owned.
**Post-Condition**:
no lock is owned.


