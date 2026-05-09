[PROMPT]
Provide complete `unlock.c` file that implement `unlock` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
//   unlock the MCS mutex, `me` will be changed to point to the next node in the queue
void mcs_mutex_unlock(mcs_mutex_t *impl, mcs_node_t *me);
```

[GUARANTEE]
```c
void unlock(struct inode* inum);
```

[SPECIFICATION]
**Pre-Condition**:
  - `inum` points to a valid `inode` structure that has been previously initialized.
  - The `inode` lock associated with `inum` is currently held by the calling thread.
  - `inum->hd` points to the valid `mcs_node_t` that was used by the current thread to acquire the lock.
**Post-Condition**:
  - The MCS lock associated with the `inode` is released, potentially allowing another waiting thread to acquire it.
  - The `inum->mutex` flag is cleared to 0.
  - The memory allocated for the `mcs_node_t` (pointed to by `inum->hd`) is deallocated.
  - The function has no return value.

**System Algorithm**:
1. Acquire the pointer to the `mcs_node_t` structure from the `hd` field of the `inode`.
2. Clear the `mutex` field of the `inode`.
3. Call `mcs_mutex_unlock` with the `impl` field of the `inode` and the acquired `mcs_node_t` pointer to release the lock.
4. Free the memory allocated for the `mcs_node_t` structure.
