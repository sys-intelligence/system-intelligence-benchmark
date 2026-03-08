[PROMPT]
Provide complete `locate.c` file that implement `locate` operation. You can use information first from [RELY], [GUARANTEE] and [SPECIFICATION] in the first phase, then more information in the refine phase as described below. Only provide the implementation of that single function and only include `path.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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

[GUARANTEE]
```c
struct inode* locate(struct inode* cur, char* path[]);
```

[SPECIFICATION]
**Pre-Condition**:
- `cur` points to a valid directory inode (access to `cur->dir` is safe).
- `path` is a valid NULL-terminated array of path component strings (each `path[i]` is a non-NULL string).
**Post-Condition**:
- **Case 1 (Empty path)**: If `path[0] == NULL`, returns the original locked `cur`.
- **Case 2 (Full traversal)**: All components are successfully traversed. Returns the inode of the final path component.
- **Case 3 (Component missing)**: A component `path[i]` is not found during traversal. Returns `NULL`.


## Refine Prompt
[RELY]
```c
void lock(struct inode* inum);
```
```c
void unlock(struct inode* inum);
```

[SPECIFICATION of locate]
**Pre-Condition**:
cur is locked.
**Post-Condition**:
If the operation succeeds, the returned inode is locked. 
If the operation fails, all locks are released.

**System Algorithm**:
1.  **Initialization**:
    * Set a pointer `current` to the starting inode `cur`. The lock on `current` is already held.
    * Start iterating through the `path` array from the first element.

2.  **Iterative Traversal Loop**: For each `name` in the `path`:
    * **a. Find Next Inode**: Perform the non-locking find operation: `next = inode_find(current, name)`.

    * **b. Handle Path Failure**:
        * If `next` is `NULL`, the path does not exist.
        * To meet the failure post-condition (no locks held), release the lock on the current node: `unlock(current)`.
        * Terminate the function and `return NULL`.

    * **c. Handle Path Success (Lock Coupling)**:
        * If `next` is a valid inode, proceed with the lock coupling sequence:
        * **Acquire Next Lock**: First, acquire the lock on the child/next inode: `lock(next)`.
        * **Release Current Lock**: *Only after* successfully acquiring the lock on `next`, release the lock on the parent/current inode: `unlock(current)`. This is the critical step that ensures a continuous, locked path during traversal.
        * **Advance Pointer**: Update the `current` pointer to move down the tree: `current = next`.

3.  **Successful Termination**:
    * If the loop completes without returning `NULL`, it means the entire path has been traversed successfully.
    * The `current` pointer now points to the final destination inode.
    * From the last step of the loop, the lock on this final `current` inode was acquired but never released.
    * Return the `current` pointer. The caller receives the target inode with its lock held, satisfying the success post-condition.

