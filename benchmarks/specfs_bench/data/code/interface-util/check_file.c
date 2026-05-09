#include "interface-util.h"

int check_file(struct inode *inum) {
    if (inum == NULL) {
        return 1;
    }

    if (inum->mode == DIR_MODE) {
        unlock(inum);
        return 1;
    }

    return 0;
}