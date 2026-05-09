[PROMPT]
Provide complete `check_open.c` file that implement `check_open` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface-util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
int check_open(struct inode *inum, unsigned mode);
```

[SPECIFICATION]
**Pre-Condition**:
  * `inum`: A pointer to an inode structure, which can be NULL.
  * `mode`: The file mode to be checked for compatibility.
**Post-Condition**:
**Case 1 (Success - Compatible modes)**:

  * Returns `0` if `inum` is not NULL and its mode is compatible with the provided `mode`. Compatibility is defined as:
      * `inum->mode` is `DIR_MODE` and `mode` is `DIR_MODE`.
      * `inum->mode` is not `DIR_MODE` and `mode` is not `DIR_MODE`.

**Case 2 (Failure - Incompatible modes or NULL inode)**:

  * Returns `1` if any of the following conditions are met:
      * a) `inum` is NULL.
      * b) `inum->mode` is `DIR_MODE`, but the provided `mode` is not.
      * c) `inum->mode` is not `DIR_MODE`, but the provided `mode` is.


**Invariant**: 
**Well-formedness of inode**: If `inum` is not NULL, it must point to a valid, initialized inode.

## Refine Prompt
[RELY]
```c
void lock(struct inode* inum);
```
```c
void unlock(struct inode* inum);
```

[SPECIFICATION of check_open]
**Pre-Condition**:
If `inum` is not NULL, the lock for `inum` is owned.
**Post-Condition**:
No lock is owned.


