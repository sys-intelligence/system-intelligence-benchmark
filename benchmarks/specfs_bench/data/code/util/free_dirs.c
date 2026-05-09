#include "util.h"

void free_dirs(char *dirname[]) {
    int i = 0;
    while (dirname[i] != NULL) {
        free(dirname[i]);
        i++;
    }
}