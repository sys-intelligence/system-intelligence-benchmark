[PROMPT]
Provide complete `unlock2dir.c` file that implement `unlock2dir` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
void unlock(struct inode* inum);
```

[GUARANTEE]
```c
void unlock2dir (struct inode* srcdir, struct inode* dstdir);
```

[SPECIFICATION]
**Pre-Condition**:
- `srcdir` is the source directory inode to be unlocked.
- `dstdir` is the destination directory inode to be unlocked.
**Post-Condition**:
- The function releases the locks of both the source and destination directory inodes.
- If `srcdir` and `dstdir` are the same, only one lock is released.

