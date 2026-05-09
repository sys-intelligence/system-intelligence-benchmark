[PROMPT]
Provide complete `check_file.c` file that implement `check_file` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface-util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
int check_file(struct inode *inum);
```

[SPECIFICATION]
**Pre-Condition**:
  * `inum`: A pointer to an `inode` structure that needs to be validated. The function must handle cases where `inum` is `NULL`.
**Post-Condition**:
**Case 1 (Success - Is a file)**:
  * The provided `inum` is not `NULL` and its `mode` is **not** `DIR_MODE`.
  * Returns `0`.

**Case 2 (Failure - Is not a file)**:
  * The provided `inum` is `NULL` **or** its `mode` is `DIR_MODE`.
  * Returns `1`.


**System Algorithm**:
The primary goal of this function is to verify if a given inode represents a regular file, not a directory.

## Refine Prompt
[RELY]
```c
void unlock(struct inode* inum);
```

[SPECIFICATION of check_file]
**Pre-Condition**:
  * If `inum` is not `NULL`, the lock for `inum` **must be held** by the caller.
**Post-Condition**:
  * If the function returns `0` (Success - Is a file), the lock for `inum` **is still held**.
  * If the function returns `1` because `inum` is a directory, the lock for `inum` **is released**.
  * If the function returns `1` because `inum` is `NULL`, no lock operation occurs.


