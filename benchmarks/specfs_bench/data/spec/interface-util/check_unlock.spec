[PROMPT]
Provide complete `check_unlock.c` file that implement `check_unlock` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `interface-util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
void unlock(struct inode* inum);
```

[GUARANTEE]
```c
void check_unlock (struct inode* parent, struct inode* src, struct inode* dst);
```

[SPECIFICATION]
**Pre-Condition**:
- `parent`, `src`, and `dst` are non-NULL inode pointers
- `parent`  is currently locked
**Post-Condition**:
The function conditionally unlocks `parent` based on pointer comparison:

- **Case 1 (Unlock performed)**:
  If `parent` distinct from both `src` and `dst`, `parent` is unlocked.
- **Case 2 (No unlock)**:
  If  `parent == src` OR `parent == dst`, no operation occurs.

