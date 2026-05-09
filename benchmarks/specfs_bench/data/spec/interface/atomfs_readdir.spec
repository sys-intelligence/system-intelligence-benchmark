[PROMPT]
Provide complete `atomfs_readdir.c` file that implement `atomfs_readdir` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
int check_dir(struct inode *inum);
```
```c
char** malloc_dir_content(unsigned size);
```
```c
void fill_dir(struct inode* inum, char** dircontent);
```
```c
typedef struct dirtb {
	struct entry *tb[DIRTB_NUM];
} dirtb;
```

[GUARANTEE]
```c
char **atomfs_readdir(char *path[]);
```

[SPECIFICATION]
**Pre-Condition**:
  * `path` must be a valid NULL-terminated array of strings representing the path to the directory.
**Post-Condition**:
**Case 1 (Successful read)**:

  * Starting from `root_inum`, the path successfully resolves to a valid directory inode.
  * An array of strings of size `target->size + 1`(should plus 1 for NULL-terminated property), with the last element being NULL, is allocated and returned, containing the names of the entries in that directory.

**Case 2 (Failure)**:

  * Returns `NULL` if either:
    a) The path traversal fails (`locate` returns NULL).
    b) The target inode is not a directory (`check_dir` returns a non-zero value).


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
If `target` is `NULL`, all locks acquired during traversal have been released.
If `target` is not `NULL`, only the lock for `target` is held. All other intermediate locks have been released.



[SPECIFICATION of check_dir]
**Pre-Condition**:
`inum` is locked.
**Post-Condition**:
If `check_dir` returns 0 (success), the lock on `inum` is still held.
If `check_dir` returns 1 (failure), the lock on `inum` has been released.


[SPECIFICATION of atomfs_readdir]
**Pre-Condition**:
No lock is held.
**Post-Condition**:
No lock is held.


