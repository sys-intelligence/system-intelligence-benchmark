[PROMPT]
Provide complete `check_ins.c` file that implement `check_ins` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface-util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

## First Prompt
[RELY]
```c
struct inode *inode_find(struct inode *node, char *name);
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
```c
typedef struct dirtb {
	struct entry *tb[DIRTB_NUM];
} dirtb;
```

[GUARANTEE]
```c
int check_ins(struct inode *cur, char *name);
```

[SPECIFICATION]
**Pre-Condition**:
  * `cur`: A pointer to the target directory inode where the insertion is proposed.
  * `name`: A valid, non-NULL string for the new entry's name.
**Post-Condition**:
**Case 1 (Success - Insertion is possible)**:
  * Returns `0` if all the following conditions are met:
      * `cur` is a valid directory (`cur->mode == DIR_MODE`).
      * The directory `cur` is not full (`cur->size < MAX_DIR_SIZE`).
      * An entry with `name` does not already exist in `cur`'s directory (check via `inode_find`).
  * The state of `cur` and its contents remains unchanged.

**Case 2 (Failure - Insertion is not possible)**:
  * Returns `1` if any of the following conditions are true:
      * `cur` is `NULL`.
      * `cur` is not a directory (`cur->mode != DIR_MODE`).
      * The directory `cur` is already full (`cur->size >= MAX_DIR_SIZE`).
      * An entry with the given `name` already exists in `cur`.


**System Algorithm**:
To validate whether a new directory entry can be created within a parent directory inode `cur`.

## Refine Prompt
[RELY]
```c
void lock(struct inode* inum);
```
```c
void unlock(struct inode* inum);
```

[SPECIFICATION of check_ins]
**Pre-Condition**:
The lock for the inode `cur` is held by the calling thread.
**Post-Condition**:
  * If the function returns `0` (Success), the lock for `cur` remains held.
  * If the function returns `1` (Failure), the lock for `cur` is released before returning.


