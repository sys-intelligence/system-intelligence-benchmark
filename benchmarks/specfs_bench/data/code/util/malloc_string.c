#include "util.h"

char* malloc_string(const char* name) {
    size_t len = strlen(name);
    char* str = malloc(len + 1);
    strcpy(str, name);
    return str;
}