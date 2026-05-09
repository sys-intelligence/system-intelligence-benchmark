#include "util.h"

void split_dirs(const char *path, char *dirname[]) {
    char *temp = malloc_string(path);
    char *saveptr;
    char *token;
    int i = 0;

    token = strtok_r(temp, "/", &saveptr);
    while (token != NULL) {
        assert(i < MAX_PATH_LEN);
        assert(strlen(token) <= MAX_FILE_LEN);
        dirname[i] = malloc_string(token);
        i++;
        token = strtok_r(NULL, "/", &saveptr);
    }
    free(temp);
}