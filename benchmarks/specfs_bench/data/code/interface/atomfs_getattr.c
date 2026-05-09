#include "interface.h"

extern struct inode* root_inum;

struct getattr_ret* atomfs_getattr(char* path[]) {
    struct inode* target;
    struct getattr_ret* ret;
    
    lock(root_inum);
    
    target = locate(root_inum, path);
    
    if (target == NULL) {
        return NULL;
    }
    
    ret = malloc_getattr_ret(target, target->mode, target->size, target->maj, target->min);
    
    unlock(target);
    
    return ret;
}