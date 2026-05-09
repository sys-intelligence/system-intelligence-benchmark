#include "path.h"

struct inode* locate_hold(struct inode *cur, char *path[]) {
    if (path[0] == NULL) {
        return cur;
    }
    
    struct inode *next = inode_find(cur, path[0]);
    
    if (next == NULL) {
        return NULL;
    }
    
    lock(next);
    
    return locate(next, &path[1]);
}