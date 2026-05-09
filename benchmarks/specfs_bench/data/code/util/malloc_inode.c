#include "util.h"

struct inode* malloc_inode(int mode, unsigned maj, unsigned min) {
    struct inode *ino = malloc(sizeof(struct inode));
    if (ino == NULL) {
        return NULL;
    }

    memset(ino, 0, sizeof(struct inode));

    ino->mode = mode;
    ino->maj = maj;
    ino->min = min;
    ino->impl = mcs_mutex_create();

    if (mode == DIR_MODE) {
        ino->dir = malloc(sizeof(struct dirtb));
        if (ino->dir != NULL) {
            memset(ino->dir, 0, sizeof(struct dirtb));
        }
    } else {
        ino->file = malloc(sizeof(struct indextb));
        if (ino->file != NULL) {
            memset(ino->file, 0, sizeof(struct indextb));
        }
    }

    return ino;
}