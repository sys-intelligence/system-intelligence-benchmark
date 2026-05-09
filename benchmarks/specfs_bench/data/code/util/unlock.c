#include "util.h"

void unlock(struct inode* inum) {
    struct mcs_node *me = inum->hd;
    inum->mutex = 0;
    mcs_mutex_unlock(inum->impl, me);
    free(me);
}