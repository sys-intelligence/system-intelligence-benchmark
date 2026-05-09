#include "interface-util.h"

int check_src_exist_dst_delete(struct inode *srcdir, struct inode *dstdir, char *srcname, char *dstname) {
    struct inode *srcinode = NULL;
    struct inode *dstinode = NULL;
    
    // Find srcinode
    srcinode = inode_find(srcdir, srcname);
    if (srcinode == NULL) {
        unlock2dir(srcdir, dstdir);
        return 1;
    }
    
    // Check dstdir validity
    if (dstdir->mode != DIR_MODE || dstdir->size >= MAX_DIR_SIZE) {
        unlock2dir(srcdir, dstdir);
        return 1;
    }
    
    // Check if dstinode exists
    dstinode = inode_find(dstdir, dstname);
    
    if (dstinode != NULL) {
        // Acquire locks for srcinode and dstinode
        // Handle case where srcinode == dstinode to avoid double-locking
        if (srcinode == dstinode) {
            lock(srcinode);
        } else {
            lock(srcinode);
            lock(dstinode);
        }
        
        // Check if same inode
        if (srcinode != dstinode) {
            // Check type compatibility
            int src_is_dir = (srcinode->mode == DIR_MODE);
            int dst_is_dir = (dstinode->mode == DIR_MODE);
            
            if (src_is_dir != dst_is_dir) {
                unlock(srcinode);
                unlock(dstinode);
                unlock2dir(srcdir, dstdir);
                return 1;
            }
            
            // If dstinode is directory, check it's empty
            if (dst_is_dir && dstinode->size != 0) {
                unlock(srcinode);
                unlock(dstinode);
                unlock2dir(srcdir, dstdir);
                return 1;
            }
        }
        
        // Release srcinode lock, keep dstinode lock
        // If srcinode == dstinode, do NOT unlock (dstinode lock must remain held)
        if (srcinode != dstinode) {
            unlock(srcinode);
        }
        // dstinode lock remains held
    } else {
        // No dstinode, no additional checks needed
        // srcinode was never locked, so nothing to unlock
    }
    
    // Success - srcdir and dstdir locks remain held
    return 0;
}