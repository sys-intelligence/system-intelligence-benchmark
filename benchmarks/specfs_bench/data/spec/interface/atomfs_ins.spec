[PROMPT]
Provide complete `atomfs_ins.c` file that implement `atomfs_ins` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
// initialize a new inode. Its `mode`, `maj`, `min` fields are filled with the arguments. the return value is non-NULL.
```c
struct inode* malloc_inode(int mode, unsigned maj, unsigned min);
```
// Check whether name can be successfully inserted to cur. If the insertion can succeed, the return value is 0. If the insertion should fail, the return value is 1.
```c
int check_ins(struct inode *cur, char *name);
```
// a new entry is inserted to cur, whose fields are specified by inum and name.
```c
int inode_insert(struct inode* cur, struct inode* inum, char* name);
```

[GUARANTEE]
```c
int atomfs_ins(char* path[], char* name, int mode, unsigned maj, unsigned min);
```

[SPECIFICATION]
**Pre-Condition**:
- `name` must be a valid string (non-NULL) for the new entry.
- `path` must be a valid NULL-terminated array of strings
**Post-Condition**:
**Case 1 (Successful traversal and insertion)**:

- A new inode with specified `mode`, `maj`, and `min` is allocated.
- The new entry `(name, inode)` is inserted into the target directory.
- Returns `0` to indicate success.

**Case 2 (Traversal or insertion failure)**:

- Returns `-1` if either:
  a) The path traversal fails (starting from `root_inum`, by following the path, `locate` returns NULL).
  b) Insertion check fails (`check_ins` returns non-zero).

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
cur is locked.
**Post-Condition**:
If target is NULL, locate would have released all locks, so no lock is owned in this case.
If target is not NULL, only the lock of target is owned. locate would have released all other locks.


[SPECIFICATION of check_ins]
**Pre-Condition**:
cur is locked.
**Post-Condition**:
if check_ins returns 0, cur is locked. 
If check_ins returns 1, no lock is owned.


[SPECIFICATION of atomfs_ins]
**Pre-Condition**:
no lock is owned. 
**Post-Condition**:
no lock is owned. 


