#include "interface.h"

int atomfs_write(char* path[], const char* buf, unsigned size, unsigned offset) {
    struct inode *inum;

    // Pre-condition: no lock is owned.
    // locate requires cur (root_inum) to be locked.
    lock(root_inum);

    // locate releases root_inum lock and acquires inum lock if found.
    // If not found, all locks are released.
    inum = locate(root_inum, path);

    if (inum == NULL) {
        // locate released all locks.
        return -1;
    }

    // check_file expects inum to be locked if not NULL.
    // Returns 1 if not writable, releasing the lock.
    // Returns 0 if writable, keeping the lock.
    if (check_file(inum) == 1) {
        // check_file released the lock on failure.
        return -1;
    }

    // check_file returned 0, inum is still locked.
    unsigned written = inode_write(inum, buf, size, offset);

    // Post-condition: no lock is owned.
    unlock(inum);

    return written;
}