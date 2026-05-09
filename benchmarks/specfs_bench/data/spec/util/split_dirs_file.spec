[PROMPT]
Provide complete `split_dirs_file.c` file that implement `split_dirs_file` operation. You can use information from [RELY], [GUARANTEE] and [SPECIFICATION] as described below. Only provide the implementation of that single function and only include `util.h` as the header. Your output is wrapped in a C code block, and no other unrelavent code should be given.

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
void split_dirs_file(const char *path, char *dirname[], char *filename);
```

[SPECIFICATION]
**Pre-Condition**:
  - `path`: A non-NULL, null-terminated string representing an absolute file path (e.g., `/a/b/c`).
  - `dirname`: A valid pointer to an array of `char*` pointers, initialized to `NULL`s, with a size of at least `MAX_PATH_LEN`.
  - `filename`: A valid pointer to a character buffer, with a size of at least `MAX_FILE_LEN`.
**Post-Condition**:
  - **Case 1: Path contains directories and a file (e.g., `/a/b/c`)**
      - The `dirname` array is populated with newly allocated strings for each directory component (`"a"`, `"b"`).
      - The entry in `dirname` following the last directory component is set to `NULL`.
      - The `filename` buffer is updated to contain the final component of the path (`"c"`).
  - **Case 2: Path contains only a filename (e.g., `/c`)**
      - The `dirname` array remains unmodified (all `NULL`s).
      - The `filename` buffer is updated to contain the file's name (`"c"`).
  - **Case 3: Path is empty or root (`/`)**
      - Both `dirname` and `filename` remain unmodified.

**System Algorithm**:
1.  **Duplicate Path**: Create a temporary, modifiable copy of the input `path` string.
2.  **Tokenize**: Use `strtok_r` to iteratively split the copied path by the `/` delimiter.
3.  **Populate Directories**: For each token found:
      - Allocate new memory for the token using `malloc_string`.
      - Store the pointer to the new string in the next available slot of the `dirname` array.
4.  **Isolate Filename**: After tokenization is complete:
      - If any tokens were found, identify the last token that was added to `dirname`.
      - Copy this last token's string content into the `filename` buffer.
      - Free the memory for this last token within the `dirname` array and set its corresponding pointer to `NULL`.
5.  **Cleanup**: Free the temporary copy of the path string created in step 1.
