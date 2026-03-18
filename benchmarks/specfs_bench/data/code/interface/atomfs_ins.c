#include "interface.h"

int atomfs_ins(char* path[], char* name, int mode, unsigned maj, unsigned min) {
    struct inode *cur;
    
    // Lock root_inum before starting traversal
    lock(root_inum);
    
    // Traverse the path to find the target directory
    cur = locate(root_inum, path);
    
    // If locate returns NULL, all locks are released, return failure
    if (cur == NULL) {
        return -1;
    }
    
    // Check if insertion is possible
    if (check_ins(cur, name) != 0) {
        // check_ins releases lock if it returns non-zero
        return -1;
    }
    
    // At this point, cur is still locked (check_ins returned 0)
    // Allocate new inode
    struct inode *new_inode = malloc_inode(mode, maj, min);
    
    // Insert the new inode into the directory
    if (inode_insert(cur, new_inode, name) != 0) {
        unlock(cur);
        return -1;
    }
    
    // Release the lock on cur before returning
    unlock(cur);
    
    return 0;
}