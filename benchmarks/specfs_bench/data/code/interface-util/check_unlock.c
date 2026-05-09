#include "interface-util.h"

void check_unlock(struct inode* parent, struct inode* src, struct inode* dst) {
    if (parent != src && parent != dst) {
        unlock(parent);
    }
}