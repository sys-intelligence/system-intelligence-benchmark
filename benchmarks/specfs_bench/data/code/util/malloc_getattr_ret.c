#include "util.h"

struct getattr_ret* malloc_getattr_ret(struct inode* inum, unsigned mode, unsigned size, unsigned maj, unsigned min) {
    struct getattr_ret* ret = malloc(sizeof(struct getattr_ret));
    if (ret == NULL) {
        return NULL;
    }

    ret->inum = inum;
    ret->mode = mode;
    ret->size = size;
    ret->maj = maj;
    ret->min = min;

    if (mode == DIR_MODE) {
        ret->maj = 0;
        ret->min = 0;
    }

    return ret;
}