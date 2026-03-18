#include "util.h"

struct read_ret* malloc_readret() {
    struct read_ret* ptr = malloc(sizeof(struct read_ret));
    if (ptr != NULL) {
        ptr->buf = NULL;
        ptr->num = 0;
    }
    return ptr;
}