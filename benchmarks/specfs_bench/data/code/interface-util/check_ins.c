#include "interface-util.h"

int check_ins(struct inode *cur, char *name) {
    if (cur == NULL) {
        return 1;
    }

    if (cur->mode != DIR_MODE) {
        unlock(cur);
        return 1;
    }

    if (cur->size >= MAX_DIR_SIZE) {
        unlock(cur);
        return 1;
    }

    if (inode_find(cur, name) != NULL) {
        unlock(cur);
        return 1;
    }

    return 0;
}