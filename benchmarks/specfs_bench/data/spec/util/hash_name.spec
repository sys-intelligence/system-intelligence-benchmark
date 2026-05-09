[PROMPT]
Provide complete `hash_name.c` file that implement `hash_name` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[GUARANTEE]
```c
unsigned int hash_name(char* name);
```

[SPECIFICATION]
**Pre-Condition**:
- `name` points to a valid null-terminated string (or is `NULL`).
**Post-Condition**:
The function returns an unsigned integer hash value in the range `[0, 0x1ff]` (0–511). Two cases define the computation:

- **Case 1 (`name` is `NULL` or empty string)**:
  Returns `0` (initial `hash` value remains unchanged).

- Case 2 (`name` points to a non-empty string):

  Computes the hash through an iterative polynomial algorithm:

  ```plaintext
  hash = (hash * 131) + current_character  
  ```

  for each character until \0 (the algorithm uses a fixed seed value `131`). Final result is hash & 0x1ff (9 least significant bits).


