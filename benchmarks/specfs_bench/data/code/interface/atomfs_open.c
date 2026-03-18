#include "interface.h"

struct inode *atomfs_open(char *path[], unsigned mode) {
    struct inode *target;
    
    lock(root_inum);
    target = locate(root_inum, path);
    
    if (target == NULL) {
        return NULL;
    }
    
    if (check_open(target, mode) != 0) {
        return NULL;
    }
    
    return target;
}