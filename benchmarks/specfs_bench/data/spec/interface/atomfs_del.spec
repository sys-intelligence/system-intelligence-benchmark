[PROMPT]
Provide complete `atomfs_del.c` file that implement `atomfs_del` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
// Check if the inode with the given name can be deleted under the current inode. Returns 0 if deletion is allowed, 1 otherwise while releasing the lock.
```c
int check_del(struct inode *cur, char *name);
```
// Delete the inode with the given name under inum. Returns the deleted inode if successful, NULL otherwise.
```c
struct inode* inode_delete(struct inode* inum, char* name);
```
// Dispose of the inode, releasing all associated resources.
```c
void dispose_inode(struct inode* inum);
```

[GUARANTEE]
```c
int atomfs_del(char* path[], char* name);
```

[SPECIFICATION]
**Pre-Condition**:
- `path`: A NULL-terminated string array representing the path to the parent directory.
- `name`: A valid, non-null string representing the name of the file or directory to be deleted.
**Post-Condition**:
Case 1 (Successful Deletion):
- The directory entry corresponding to `name` is removed from the target directory found at `path`.
- The inode previously associated with `name` is deallocated.
- Returns 0.

Case 2 (Failure):
- The file system state remains unchanged.
- Returns `-1` if the path traversal fails (starting from `root_inum`, by following the `path` via `locate`, it returns `NULL`) or the deletion check fails (check_del returns a non-zero value).

**Invariant**: 
Root Existence: The global `root_inum` must always point to a valid, initialized directory inode.

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
The `cur` inode must be locked.
**Post-Condition**:
If a target inode is returned, it is locked, and all intermediate locks (including the initial lock on `cur`) have been released. If `NULL` is returned, all locks have been released.


[SPECIFICATION of check_del]
**Pre-Condition**:
The `cur` inode must be locked.
**Post-Condition**:
If the function returns 0 (success), the lock on `cur` is still held. If it returns non-zero (failure), the lock on `cur` is released.


[SPECIFICATION of atomfs_del]
**Pre-Condition**:
No lock is owned.
**Post-Condition**:
No lock is owned.


