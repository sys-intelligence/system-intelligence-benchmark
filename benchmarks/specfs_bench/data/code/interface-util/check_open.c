#include "interface-util.h"

int check_open(struct inode *inum, unsigned mode) {
    int result = 1;

    if (inum != NULL) {
        int inum_is_dir = (inum->mode == DIR_MODE);
        int mode_is_dir = (mode == DIR_MODE);

        if (inum_is_dir == mode_is_dir) {
            result = 0;
        }

        unlock(inum);
    }

    return result;
}