#include "interface-util.h"

int check_del(struct inode *cur, char *name) {
    struct inode *target;

    // Pre-condition: cur lock is already held

    if (cur == NULL) {
        return 1;
    }

    target = inode_find(cur, name);

    if (target == NULL) {
        unlock(cur);
        return 1;
    }

    // Check if deletion is permissible (file or empty directory)
    if (target->mode != DIR_MODE || target->size == 0) {
        // Success: lock target, return with both locks held
        lock(target);
        return 0;
    } else {
        // Failure: non-empty directory, release cur lock
        unlock(cur);
        return 1;
    }
}