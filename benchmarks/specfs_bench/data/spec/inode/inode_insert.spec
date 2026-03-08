[PROMPT]
Provide complete `inode_insert.c` file that implement `inode_insert` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `inode.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
char* malloc_string(const char* name);
```
```c
unsigned int hash_name(char* name);
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
```c
typedef struct entry {
	char *name;
	void *inum;
	struct entry *next;
} entry;
```
```c
struct entry *malloc_entry();
```

[GUARANTEE]
```c
int inode_insert(struct inode* cur, struct inode* inum, char* name);
```

[SPECIFICATION]
**Pre-Condition**:
there exists an inode pointed to by `cur`. The `dir` field of `cur`records a fixed length array of heads of entry lists.
**Post-Condition**:
Case1: if the operation succeeds, a new `entry` is inserted into `cur` inode, whose fields are specified by the arguments of `inode_insert`. The new `entry` locates at the head of `cur->dir->tb[n]` where `n` is computed by `hash_name(name)`.  The size of `cur` increases by 1. The return value is 0.
Case2: if the operation fails due to memory allocation failures, unused memory is freed and the return value is 1.

