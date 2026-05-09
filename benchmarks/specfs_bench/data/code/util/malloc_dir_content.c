#include "util.h"

char** malloc_dir_content(unsigned size) {
    return (char**)malloc(size * sizeof(char*));
}