#include "util.h"

char** calculate(char* srcpath[], char* dstpath[]) {
    unsigned i = 0;
    while (srcpath[i] != NULL && dstpath[i] != NULL) {
        const char *s = srcpath[i];
        const char *d = dstpath[i];
        while (*s == *d) {
            if (*s == '\0') {
                break;
            }
            s++;
            d++;
        }
        if (*s != *d) {
            break;
        }
        i++;
    }

    char** compath = malloc_path(i + 1);
    for (unsigned j = 0; j < i; j++) {
        compath[j] = malloc_string(srcpath[j]);
    }
    compath[i] = NULL;

    return compath;
}