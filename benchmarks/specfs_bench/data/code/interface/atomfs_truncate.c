#include "interface.h"

int atomfs_truncate(char* path[], unsigned offset) {
    struct inode *target;
    
    // Check if offset exceeds maximum file size
    if (offset > MAX_FILE_SIZE) {
        return -1;
    }
    
    // Lock root and locate the target inode
    lock(root_inum);
    target = locate(root_inum, path);
    
    // If path traversal failed, return error
    if (target == NULL) {
        return -1;
    }
    
    // Verify it's a regular file
    // Note: check_file releases lock on failure, keeps lock on success
    if (check_file(target) != 0) {
        return -1;
    }
    
    // Truncate the file (inode_truncate keeps lock)
    inode_truncate(target, offset);
    
    // Release lock and return success
    unlock(target);
    return 0;
}