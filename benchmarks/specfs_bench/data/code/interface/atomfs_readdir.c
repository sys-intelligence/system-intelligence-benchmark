#include "interface.h"

char **atomfs_readdir(char *path[]) {
    struct inode *target = NULL;
    char **dircontent = NULL;

    // Lock root_inum before calling locate (as per locate's pre-condition)
    lock(root_inum);

    // Locate the inode; if successful, the lock on 'target' is acquired.
    target = locate(root_inum, path);

    // Case 2a: Path traversal failed.
    if (target == NULL) {
        // locate already released all locks including root_inum
        return NULL;
    }

    // Check if 'target' is a directory.
    // If check_dir returns non-zero, it releases the lock on 'target'.
    if (check_dir(target) != 0) {
        return NULL;
    }

    // Allocate memory for directory content (size + 1 for NULL termination).
    dircontent = malloc_dir_content(target->size + 1);

    // Handle allocation failure.
    if (dircontent == NULL) {
        unlock(target);
        return NULL;
    }

    // Fill the directory content.
    fill_dir(target, dircontent);

    // Post-condition: No lock is held. Release the lock on 'target'.
    unlock(target);

    return dircontent;
}