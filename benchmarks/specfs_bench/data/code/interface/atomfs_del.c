#include "interface.h"

int atomfs_del(char* path[], char* name) {
    struct inode *parent;
    
    // Lock root and traverse to parent directory
    lock(root_inum);
    parent = locate(root_inum, path);
    
    // If path traversal failed, return error (locate already released all locks)
    if (parent == NULL) {
        return -1;
    }
    
    // Check if deletion is allowed
    // If check_del returns 0, parent lock is still held
    // If check_del returns non-zero, parent lock is released
    int del_check = check_del(parent, name);
    if (del_check != 0) {
        // check_del already released the lock on failure
        return -1;
    }
    
    // Delete the inode (parent still locked from check_del success)
    struct inode *deleted = inode_delete(parent, name);
    
    // Dispose of the deleted inode if successful
    if (deleted != NULL) {
        dispose_inode(deleted);
    }
    
    // Release parent lock (check_del succeeded, so lock was still held)
    unlock(parent);
    
    return 0;
}