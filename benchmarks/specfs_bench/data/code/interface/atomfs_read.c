#include "interface.h"

struct read_ret* atomfs_read(char* path[], unsigned size, unsigned offset) {
    struct inode *inum;
    
    lock(root_inum);
    inum = locate(root_inum, path);
    
    if (inum == NULL || check_file(inum) != 0) {
        return NULL;
    }
    
    struct read_ret *result = inode_read(inum, size, offset);
    unlock(inum);
    
    return result;
}