#include "util.h"

char** malloc_path(unsigned len) {
    char** paths = calloc(len, sizeof(char*));
    return paths;
}