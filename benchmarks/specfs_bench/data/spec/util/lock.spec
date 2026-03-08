[PROMPT]
Provide complete `lock.c` file that implement `lock` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
typedef struct mcs_node {
    //  ... other fields ...
} mcs_node_t;
```
```c
//  lock a mutex
int mcs_mutex_lock(mcs_mutex_t *impl, mcs_node_t *me);
```
```c
extern long syscall(long __sysno, ...);
```
```c
//  The standard C library function `malloc` for dynamic memory allocation
extern void *malloc(size_t __size)
```

[GUARANTEE]
```c
void lock(struct inode* inum);
```

[SPECIFICATION]
**Pre-Condition**:
- `inum` is a non-NULL pointer to a valid, initialized `inode` structure.
- The `inum->impl` field must point to a valid MCS lock object.
**Post-Condition**:
- A new `mcs_node_t` is allocated and associated with the calling thread for this lock acquisition.
- `inum->hd` is updated to point to the `mcs_node_t` of the calling thread.
- `inum->mutex` is updated to the thread ID (tid) of the calling thread, marking it as the lock owner.

**System Algorithm**:
- Allocate a new MCS queue node for the current thread.
- Invoke the underlying `mcs_mutex_lock` function to perform the atomic lock acquisition.
- Once the lock is acquired, update the `inode`'s `hd` and `mutex` (via `syscall(SYS_gettid)`) fields to record the current thread as the owner.
