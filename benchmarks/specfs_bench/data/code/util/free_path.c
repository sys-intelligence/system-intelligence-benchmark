#include "util.h"

void free_path(char** path) {
    if (path == NULL) {
        return;
    }

    for (int i = 0; path[i] != NULL; i++) {
        free(path[i]);
    }

    free(path);
}