[PROMPT]
Provide complete `dispose_inode.c` file that implement `dispose_inode` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
typedef struct entry {
	char *name;
	void *inum;
	struct entry *next;
} entry;
```
```c
typedef struct indextb {
	unsigned char *index[INDEXTB_NUM];
} indextb;
```
```c
typedef struct dirtb {
	struct entry *tb[DIRTB_NUM];
} dirtb;
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
```c
//   destroy a mutex
int mcs_mutex_destroy(mcs_mutex_t *lock);
```

[GUARANTEE]
```c
void dispose_inode(struct inode* inum);
```

[SPECIFICATION]
**Pre-Condition**:
- `inum` is a pointer to an `inode` structure.
**Post-Condition**:
- Remove the inode contents. If it's a directory, free the directory table. If it's a file, free the index table.
- Destroy the mutex associated with the inode.
- Free the inode structure itself.

