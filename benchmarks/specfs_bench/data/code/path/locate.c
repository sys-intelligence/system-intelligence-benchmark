#include "path.h"

struct inode* locate(struct inode* cur, char* path[]) {
    struct inode* current = cur;
    
    // Handle empty path case
    if (path[0] == NULL) {
        return current;
    }
    
    // Iterate through path components
    for (int i = 0; path[i] != NULL; i++) {
        char* name = path[i];
        
        // Find next inode (non-locking operation)
        struct inode* next = inode_find(current, name);
        
        // Handle path failure
        if (next == NULL) {
            unlock(current);
            return NULL;
        }
        
        // Lock coupling: acquire next lock before releasing current
        lock(next);
        unlock(current);
        
        // Advance to next node
        current = next;
    }
    
    // Successfully traversed entire path, current is locked
    return current;
}