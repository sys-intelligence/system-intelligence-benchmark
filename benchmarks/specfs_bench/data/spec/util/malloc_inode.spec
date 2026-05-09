[PROMPT]
Provide complete `malloc_inode.c` file that implement `malloc_inode` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
//malloc and return mcs_mutex. The return value is non-NULL.
struct mcs_mutex * mcs_mutex_create();
```

[GUARANTEE]
```c
struct inode* malloc_inode(int mode, unsigned maj, unsigned min);
```

[SPECIFICATION]
**Pre-Condition**:
Returns a pointer to a newly allocated and initialized `inode` structure. Three initialization cases exist:

1. Case 1 (Regular file) (mode != DIR_MODE):
   - `file` field allocated and initialized to a zeroed `indextb`
   - `dir` field remains NULL
2. Case 2 (Directory) (mode == DIR_MODE):
   - `dir` field allocated and initialized to a zeroed `dirtb`
   - `file` field remains NULL
3. Common initialization:
   - All inode fields zeroed (The entire `inode` is zero-initialized with `memset()`) except:
     - `mode`, `maj`, and `min` set to input arguments
     - `impl` initialized to a new MCS mutex via `mcs_mutex_create()`
**Post-Condition**:
1. Case 1 (Regular file) (mode != DIR_MODE):
   - `file` field allocated and initialized to a zeroed `indextb`
   - `dir` field remains NULL
2. Case 2 (Directory) (mode == DIR_MODE):
   - `dir` field allocated and initialized to a zeroed `dirtb`
   - `file` field remains NULL
3. Common initialization:
   - All inode fields zeroed (The entire `inode` is zero-initialized with `memset()`) except:
     - `mode`, `maj`, and `min` set to input arguments
     - `impl` initialized to a new MCS mutex via `mcs_mutex_create()`

