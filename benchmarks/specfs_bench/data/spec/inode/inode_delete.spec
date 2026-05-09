[PROMPT]
Provide complete `inode_delete.c` file that implement `inode_delete` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `inode.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
unsigned int hash_name(char* name);
```
```c
void free_entry(struct entry* en);
```
```c
typedef struct entry {
	char *name;
	void *inum;
	struct entry *next;
} entry;
```
```c
typedef struct dirtb {
	struct entry *tb[DIRTB_NUM];
} dirtb;
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

[GUARANTEE]
```c
struct inode* inode_delete(struct inode* inum, char* name);
```

[SPECIFICATION]
**Pre-Condition**:
there exists an inode pointed to by `cur`. The inode is an directory, i.e., `cur->dir` is not NULL.
**Post-Condition**:
there are two cases depending on whether the entry named `name` exists.
Case1: if an entry named `name` exists in `cur`, the entry is removed from `cur` and freed. The `inum` field of the entry is returned. The `size` of `cur` decreases by 1.
Case2: if an entry named `name` is not found in `cur`, the return value is NULL.

**Invariant**: 
**Directory well-formedness**: (1) Each child entry's name is different from others in the same directory. (2) In an inode `inode`, for each name `name`, its entry resides in the linked list of bucket `inode->dir->tb[n]`  where n is given by `hash_name(name)`.
