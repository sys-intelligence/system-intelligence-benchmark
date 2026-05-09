[PROMPT]
Provide complete `malloc_getattr_ret.c` file that implement `malloc_getattr_ret` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
typedef struct getattr_ret {
	struct inode *inum;
	unsigned mode;
	unsigned size;
	unsigned maj;
	unsigned min;
} getattr_ret;
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
struct getattr_ret* malloc_getattr_ret(struct inode* inum, unsigned mode, unsigned size, unsigned maj, unsigned min);
```

[SPECIFICATION]
**Pre-Condition**:
- `inum` is a valid pointer to an `inode` structure.
- `mode` is a valid mode for the inode.
- `size` is a valid size for the inode.
- `maj` and `min` are valid major and minor device numbers.
**Post-Condition**:
- Returns a pointer to a `getattr_ret` structure containing the attributes of the inode.
- Directories should have device numbers set to 0.

