[PROMPT]
Provide complete `check_del.c` file that implement `check_del` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `interface-util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
struct inode *inode_find(struct inode *node, char *name);
```
```c
typedef struct dirtb {
	struct entry *tb[DIRTB_NUM];
} dirtb;
```

[GUARANTEE]
```c
int check_del(struct inode *cur, char *name);
```

[SPECIFICATION]
**Pre-Condition**:
  * `cur` is a pointer to a valid directory inode.
  * `name` is a valid, non-NULL string representing the entry to be checked.
**Post-Condition**:
**Case 1 (Deletion is permissible)**:

  * The entry `name` exists in `cur`(via `inode_find`).
  * The entry is either a file or an empty directory (`mode != DIR_MODE` or `size == 0`).
  * Returns `0`.

**Case 2 (Deletion is not permissible)**:

  * Returns `1` if any of the following are true:
      * `cur` is `NULL`.
      * The entry `name` does not exist within `cur`.
      * The entry `name` is a directory that is not empty (`mode == DIR_MODE` and `size > 0`).



## Refine Prompt
[RELY]
```c
void lock(struct inode* inum);
```
```c
void unlock(struct inode* inum);
```

[SPECIFICATION of check_del]
**Pre-Condition**:
The lock for the directory inode `cur` is held.
**Post-Condition**:
** If the function returns 0 (Success)**: The lock for `cur` AND the lock for the target inode (`inum`) are held.
** If the function returns 1 (Failure)**: All locks(locks of `cur` and `inum`, if exist) are released. The caller owns no locks that were passed to or acquired in this function.



[SPECIFICATION of inode_find]
**Pre-Condition**:
No lock assumptions.
**Post-Condition**:
No locks are acquired or released.


