#include "util.h"

void unlock2dir (struct inode* srcdir, struct inode* dstdir) {
    if (srcdir == dstdir) {
        unlock(srcdir);
    } else {
        unlock(srcdir);
        unlock(dstdir);
    }
}