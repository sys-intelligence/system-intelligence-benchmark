#include "util.h"

void dispose_inode(struct inode* inum) {
    if (inum == NULL) {
        return;
    }

    // Destroy the mutex associated with the inode
    if (inum->impl != NULL) {
        mcs_mutex_destroy(inum->impl);
    }

    // Remove inode contents based on mode
    if (inum->mode == DIR_MODE && inum->dir != NULL) {
        struct dirtb *dt = inum->dir;
        for (int i = 0; i < DIRTB_NUM; i++) {
            struct entry *e = dt->tb[i];
            while (e != NULL) {
                struct entry *next = e->next;
                if (e->name != NULL) {
                    free(e->name);
                }
                free(e);
                e = next;
            }
        }
        free(dt);
    } else if (inum->mode == FILE_MODE && inum->file != NULL) {
        struct indextb *ft = inum->file;
        for (int i = 0; i < INDEXTB_NUM; i++) {
            if (ft->index[i] != NULL) {
                free(ft->index[i]);
            }
        }
        free(ft);
    }

    // Free the inode structure itself
    free(inum);
}