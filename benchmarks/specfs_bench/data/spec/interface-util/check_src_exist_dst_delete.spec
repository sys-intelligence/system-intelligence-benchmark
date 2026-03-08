[PROMPT]
Provide complete `check_src_exist_dst_delete.c` file that implement `check_src_exist_dst_delete` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface-util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
typedef struct dirtb {
	struct entry *tb[DIRTB_NUM];
} dirtb;
```
```c
struct inode *inode_find(struct inode *node, char *name);
```
```c
#define FILE_MODE 1
#define DIR_MODE 2
#define CHR_MODE 3
#define BLK_MODE 4
#define SOCK_MODE 5
#define FIFO_MODE 6
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

[GUARANTEE]
```c
int check_src_exist_dst_delete(struct inode *srcdir, struct inode *dstdir, char *srcname, char *dstname);
```

[SPECIFICATION]
**Pre-Condition**:
  - `srcdir`, `dstdir`: Non-NULL pointers to valid `inode` structures.
  - `srcname`, `dstname`: Non-NULL, NULL-terminated strings representing entry names.
**Post-Condition**:
The function checks several conditions for a rename-like operation and returns an integer status.

**Case 1 (Success)**: If all of the following conditions (1)-(3) are met, the function returns **0**.

1.  **Source Existence**: An inode named `srcname` exists under `srcdir`. Let this be `srcinode`.
2.  **Destination Directory Validity**:
      - `dstdir` must be a directory (i.e., `dstdir->mode == DIR_MODE`).
      - `dstdir` must have space for a new entry (i.e., `dstdir->size < MAX_DIR_SIZE`).
3.  **Destination Entry Validity**: If an inode named `dstname` exists under `dstdir` (let it be `dstinode`), then all of the following must be true:
      - If `srcinode` is the same as `dstinode`, the validity is held.
      - If `srcinode` is not the same as `dstinode`, then:
        - `srcinode` and `dstinode` have compatible types (either both are directories or both are not directories).
        - If `dstinode` is a directory, it must be empty (i.e., `dstinode->size == 0`).

**Case 2 (Failure)**: If any condition in Case 1 is not met, the function returns **1**.


**Invariant**: 
**Valid Directories**: The input inodes `srcdir` and `dstdir` point to valid, initialized inode structures.

## Refine Prompt
[RELY]
```c
void lock(struct inode* inum);
```
```c
void unlock(struct inode* inum);
```
// unlock the lock of srcdir and dstdir.
```c
void unlock2dir (struct inode* srcdir, struct inode* dstdir);
```

[SPECIFICATION of check_src_exist_dst_delete]
**Pre-Condition**:
  - The caller must hold the locks for both `srcdir` and `dstdir` before calling this function.
**Post-Condition**:
  - **On Failure (return 1)**: All locks held upon entry and acquired during execution are released. No locks are held by this function upon return.
  - **On Success (return 0)**:
      - The locks on `srcdir` and `dstdir` remain held.
      - If `dstinode` existed, its lock also remains held.
      - The lock on `srcinode` (if acquired) is released.

**System Algorithm**:
1.  Check for the existence of `srcinode` (the entry named `srcname` in `srcdir`).
2.  Check the validity of `dstdir` (mode and size).
3.  If an entry named `dstname` exists in `dstdir` (let it be `dstinode`):
      - Acquire the lock for `srcinode`.
      - Acquire the lock for `dstinode`.
      - Perform checks on `srcinode` and `dstinode` (type compatibility, directory emptiness).
      - After the checks are complete, release the lock on `srcinode`.
      - **Important**: The lock on `dstinode` is **not** released if it exists and all checks pass. It is held for the subsequent deletion operation by the caller.
4.  **Error Handling**: If any check fails at any point, release all locks currently held (`srcdir`, `dstdir`, and if acquired, `srcinode` and `dstinode`) and return.


