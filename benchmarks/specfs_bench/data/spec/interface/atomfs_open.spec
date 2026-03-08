[PROMPT]
Provide complete `atomfs_open.c` file that implement `atomfs_open` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
// Traverse path under cur. If an inode is found, the return value is the found inode. If no inode is found, the return value is NULL. The lock of cur is released before returning, and the lock of the found inode is acquired.
```c
struct inode* locate(struct inode* cur, char* path[]);
```
```c
int check_open(struct inode *inum, unsigned mode);
```

[GUARANTEE]
```c
struct inode *atomfs_open(char *path[], unsigned mode);
```

[SPECIFICATION]
**Pre-Condition**:
  * `path` must be a valid, NULL-terminated array of strings representing the file path.
  * `mode` is an unsigned integer representing the desired access mode.
**Post-Condition**:
**Case 1 (Successful open)**:

  * The path is successfully traversed to find the target inode.
  * The open check for the given mode is successful.
  * Returns a pointer to the target inode.

**Case 2 (Failure to open)**:

  * Returns `NULL` if either:
      * a) The path traversal fails (starting from `root_inum`, by following the path, `locate` returns `NULL`).
      * b) The open check fails (`check_open` returns a non-zero value).

**Invariant**: 
**Well-formedness of root_inum**: The global `root_inum` must always point to a valid, initialized directory inode.

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
  * If `locate` returns a non-NULL `target`, only the lock on `target` is held. All other intermediate locks have been released.
  * If `locate` returns `NULL`, no locks are held.


[SPECIFICATION of check_open]
**Pre-Condition**:
`inum` is locked.
**Post-Condition**:
`inum` is unlocked.


[SPECIFICATION of atomfs_open]
**Pre-Condition**:
No locks are held.
**Post-Condition**:
No locks are held.


