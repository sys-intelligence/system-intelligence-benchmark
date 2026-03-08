[PROMPT]
Provide complete `check_dir.c` file that implement `check_dir` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface-util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
#define FILE_MODE 1
#define DIR_MODE 2
#define CHR_MODE 3
#define BLK_MODE 4
#define SOCK_MODE 5
#define FIFO_MODE 6
```

[GUARANTEE]
```c
int check_dir(struct inode *inum);
```

[SPECIFICATION]
**Pre-Condition**:
  * `inum`: A pointer to a `struct inode` that needs to be validated, or `NULL`.
**Post-Condition**:
**Case 1 (Success)**:

  * The provided `inum` is not `NULL` and its `mode` field is equal to `DIR_MODE`.
  * Returns `0` to indicate that it is a valid directory.

**Case 2 (Failure)**:

  * The provided `inum` is `NULL` or its `mode` field is not equal to `DIR_MODE`.
  * Returns `1` to indicate that it is not a valid directory.


**System Algorithm**:
This function serves as a predicate to validate if a given inode handle represents a directory.

## Refine Prompt
[RELY]
```c
void unlock(struct inode* inum);
```

[SPECIFICATION of check_dir]
**Pre-Condition**:
  * If `inum` is not `NULL`, the lock for `inum` is owned by the current thread.
**Post-Condition**:
** If the function returns 0 (Success)**: The lock for `inum` remains owned by the current thread.
** If the function returns 1 (Failure)**: No lock is owned by the current thread (specifically, if `inum` was not `NULL`, its lock has been released).



