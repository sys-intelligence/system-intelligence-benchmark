[PROMPT]
Provide complete `atomfs_rename.c` file that implement `atomfs_rename` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
// Delete the inode with the given name under inum. Returns the deleted inode if successful, NULL otherwise.
```c
struct inode* inode_delete(struct inode* inum, char* name);
```
// a new entry is inserted to cur, whose fields are specified by inum and name.
```c
int inode_insert(struct inode* cur, struct inode* inum, char* name);
```
```c
struct inode *inode_find(struct inode *node, char *name);
```
// Dispose of the inode, releasing all associated resources.
```c
void dispose_inode(struct inode* inum);
```
```c
int check_src_exist_dst_delete(struct inode *srcdir, struct inode *dstdir, char *srcname, char *dstname);
```
// malloc and return the common part of srcpath and dstpath
```c
char** calculate(char* srcpath[], char* dstpath[]);
```
```c
void free_path(char** path);
```
```c
int getlen(char* path[]);
```
```c
struct inode* locate_hold(struct inode *cur, char *path[]);
```
// Traverse path under cur. If an inode is found, the return value is the found inode. If no inode is found, the return value is NULL. The lock of cur is released before returning, and the lock of the found inode is acquired.
```c
struct inode* locate(struct inode* cur, char* path[]);
```
// unlock parent if it is not equal to src and dst
```c
void check_unlock (struct inode* parent, struct inode* src, struct inode* dst);
```

[GUARANTEE]
```c
int atomfs_rename(char* srcpath[], char* dstpath[], char* srcname, char* dstname);
```

[SPECIFICATION]
**Pre-Condition**:
  * `srcpath`, `dstpath`, `srcname`, and `dstname` are valid, non-NULL pointers.
**Post-Condition**:
There are two possible outcomes:

**Case 1 (Success)**: If all of the following conditions (1-3) are met:

1.  **Parent Directories Valid**:
      * Traversing `srcpath` from `root_inum` successfully finds a directory inode `srcdir`.
      * Traversing `dstpath` from `root_inum` successfully finds a directory inode `dstdir`.
2.  Source exists and destination is compatible.

Then the following state changes occur:

  * The entry for `srcname` is removed from `srcdir`.
  * If `dstinode` existed, it is removed from `dstdir` and its resources are disposed of.
  * A new entry for `srcinode` is created in `dstdir` with the name `dstname`.
  * The function returns **0**.

**Case 2 (Failure)**: If any of the conditions in Case 1 are not met, the file system state remains unchanged, and the function returns **-1**.


**Invariant**: 
**Well-formedness of root_inum**: The global `root_inum` must point to a valid, initialized directory inode.
**System Algorithm**:
The operation is implemented by first traversing to the source and destination parent directories, performing a series of validation checks, and then executing the move. The high-level logic is:

1.  Calculate the common path between `srcpath` and `dstpath`.
2.  Traverse from the root to the common ancestor directory (`parent`).
3.  From `parent`, traverse the remaining paths to find the source directory (`srcdir`) and destination directory (`dstdir`).
4.  Perform checks for existence, type compatibility, and other constraints on the source (`srcname`) and destination (`dstname`).
5.  If all checks pass, atomically perform the rename.
6.  Clean up any resources (e.g., the old destination inode if it was overwritten).


## Refine Prompt
[RELY]
```c
void lock(struct inode* inum);
```
```c
void unlock(struct inode* inum);
```
// Traverse path under cur. If an inode is found, the return value is the found inode. If no inode is found, the return value is NULL. The lock of cur is released before returning, and the lock of the found inode is acquired.
```c
struct inode* locate(struct inode* cur, char* path[]);
```
```c
struct inode* locate_hold(struct inode *cur, char *path[]);
```
// unlock parent if it is not equal to src and dst
```c
void check_unlock (struct inode* parent, struct inode* src, struct inode* dst);
```
// unlock the lock of srcdir and dstdir.
```c
void unlock2dir (struct inode* srcdir, struct inode* dstdir);
```

[SPECIFICATION of atomfs_rename]
**System Algorithm**:
The locking algorithm for `atomfs_rename` is divided into three distinct phases:

**Phase 1: Traverse the Common Path**

  * **Goal**: Find the lowest common ancestor directory (`parent`) of `srcdir` and `dstdir`.
  * **Algorithm**:
    1.  Acquire the lock on `root_inum`.
    2.  Invoke `locate` to traverse the common path in a lock-coupling fashion.
    3.  **Post-condition**: The lock on `parent` is held.
    4.  **Error Handling**: If traversal fails (`locate` returns NULL), no locks will be held. Return -1.

**Phase 2: Traverse Remaining Paths**

  * **Goal**: Find the `srcdir` and `dstdir` inodes.
  * **Algorithm**:
    1.  **Pre-condition**: The lock on `parent` is held.
    2.  Invoke `locate_hold` to traverse the remaining part of `srcpath` from `parent` to find `srcdir`. The lock on `parent` is held throughout.
    3.  Invoke `locate_hold` to traverse the remaining part of `dstpath` from `parent` to find `dstdir`. The lock on `parent` is held throughout.
    4.  Release the `parent` lock using `check_unlock` to avoid releasing it if it's the same as `srcdir` or `dstdir`.
    5.  **Post-condition**: The locks on `srcdir` and `dstdir` are held.
    6.  **Error Handling**: 
        If locating `srcdir` fails, release the `parent` lock and return -1.
        If locating `dstdir` fails, release the `parent` lock using `check_unlock` and the `srcdir` lock. Return -1.

**Phase 3: Checks and Operations**

  * **Goal**: Validate conditions and perform the atomic rename operation.
  * **Algorithm**:
    1.  **Pre-condition**: The locks on `srcdir` and `dstdir` are held.
    2.  Validate that the source exists and that the destination is a valid and safe target for the operation via `check_src_exist_dst_delete`.
    3.  If validation fails, return -1 (all locks will be released by `check_src_exist_dst_delete`).
    4.  Perform the rename operation:
        - Delete `srcname` from `srcdir` to get `srcinode`.
        - Delete `dstname` from `dstdir` to get `dstinode`. If `dstinode` existed, dispose of it.
        - Insert `srcinode` into `dstdir` with the name `dstname`.
    4.  After the main operations (`inode_delete`, `inode_insert`) are complete, release the locks on `srcdir` and `dstdir` using `unlock2dir`.
    5.  Return 0 on success.


[SPECIFICATION of locate]
**Pre-Condition**:
cur is locked.
**Post-Condition**:
Two cases for postcondition of locate.
Case1: If the traversal succeeds to return a target inode, only the lock of target inode is owned.
Case2: If the return value is NULL, no lock is owned.


[SPECIFICATION of locate_hold]
**Pre-Condition**:
cur is locked.
**Post-Condition**:
Two cases for postcondition of locate_hold.
Case1: If the traversal succeeds to return a target inode, the lock of target inode and cur is owned. Note: in case target and cur are the same, only one lock is owned.
Case2: if the return value is NULL, only the lock of cur is owned.


[SPECIFICATION of check_src_exist_dst_delete]
**Pre-Condition**:
The locks on both `srcdir` and `dstdir` are held before calling this function.
**Post-Condition**:
- On Failure (return 1): All locks held upon entry and acquired during execution are released. No locks are held by this function upon return.
- On Success (return 0):
  - The locks on `srcdir` and `dstdir` remain held.
  - If `dstinode` existed, its lock also remains held.
  - The lock on `srcinode` is released before returning.


