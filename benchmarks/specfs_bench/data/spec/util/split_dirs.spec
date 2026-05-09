[PROMPT]
Provide complete `split_dirs.c` file that implement `split_dirs` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

[RELY]
```c
char* malloc_string(const char* name);
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

[GUARANTEE]
```c
void split_dirs(const char *path, char *dirname[]);
```

[SPECIFICATION]
**Pre-Condition**:
  - `path`: A pointer to a valid, NULL-terminated string representing a file path (e.g., "/dir1/dir2/file").
  - `dirname`: A pointer to an array of `char*` that is large enough to hold all the components of the `path`.

**Post-Condition**:
  - The `dirname` array is populated with pointers to newly allocated strings.
  - Each string in `dirname` contains one component of the original `path`, in the order they appeared.
  - The input `path` string remains unmodified.
  - The function does not have a return value.


**System Algorithm**:
1.  Create a temporary, modifiable copy of the input `path` string.
2.  Use a tokenizing function (like `strtok_r`) to iteratively split the copied string by the `/` delimiter.
3.  For each token extracted:
    a. Assert that the number of tokens does not exceed `MAX_PATH_LEN`.
    b. Assert that the length of the token does not exceed `MAX_FILE_LEN`.
    c. Use `malloc_string` to create a dynamically allocated copy of the token.
    d. Store the pointer to this new string in the `dirname` array.
4.  Once all tokens have been processed, free the temporary copy of the path string.
