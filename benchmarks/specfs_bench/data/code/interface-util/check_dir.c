#include "interface-util.h"

int check_dir(struct inode *inum) {
    if (inum == NULL || inum->mode != DIR_MODE) {
        if (inum != NULL) {
            unlock(inum);
        }
        return 1;
    }
    return 0;
}