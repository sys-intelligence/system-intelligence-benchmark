[PROMPT]
Provide complete `fill_dir.c` file that implement `fill_dir` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
typedef struct dirtb {
	struct entry *tb[DIRTB_NUM];
} dirtb;
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
char* malloc_string(const char* name);
```

[GUARANTEE]
```c
void fill_dir(struct inode* inum, char** dircontent);
```

[SPECIFICATION]
**Pre-Condition**:
  * `inum` is a **valid pointer** to an initialized `inode` structure that represents a directory.
  * `inum->dir` points to a valid `dirtable` structure.
  * `dircontent` is a pointer to an array of `char*` that has sufficient capacity to store pointers to all entry names within the directory, plus one additional slot for a `NULL` terminator.
**Post-Condition**:
  * The `dircontent` array is filled with pointers to **newly allocated strings**, where each string is a copy of an entry's name from the directory.
  * The order of names in `dircontent` corresponds to the traversal order of the directory's hash table and linked lists.
  * The element in `dircontent` immediately following the last entry name is set to `NULL`, serving as a terminator for the list.
  * The function **does not modify** the `inode` or its associated directory structures.
  * The function returns `void`.

**System Algorithm**:
1.  Initialize two counters, `i` for iterating through the hash table buckets and `j` for indexing the `dircontent` array.
2.  Iterate through each bucket of the hash table `inum->dir->tb` from index `0` to `DIRTB_NUM - 1`.
3.  For each bucket, traverse the linked list of `entry` structures starting from the head.
4.  For each `entry` encountered in the linked list:
    a. Call `malloc_string` to create a memory-allocated copy of the entry's name (`walk->name`).
    b. Store the pointer to this new string at `dircontent[j]`.
    c. Increment the `dircontent` index `j`.
5.  After iterating through all buckets and their corresponding linked lists, place a `NULL` pointer at `dircontent[j]` to terminate the array.
