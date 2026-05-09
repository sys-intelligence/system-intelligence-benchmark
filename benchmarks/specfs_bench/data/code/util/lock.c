#include "util.h"

void lock(struct inode* inum) {
    mcs_node_t *me = (mcs_node_t *)malloc(sizeof(mcs_node_t));
    mcs_mutex_lock(inum->impl, me);
    inum->hd = me;
    inum->mutex = syscall(SYS_gettid);
}