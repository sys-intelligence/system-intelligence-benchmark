#include "interface.h"

int atomfs_rename(char* srcpath[], char* dstpath[], char* srcname, char* dstname) {
    int ret = -1;
    struct inode* srcdir = NULL;
    struct inode* dstdir = NULL;
    int src_suffix_len = 0;
    int dst_suffix_len = 0;
    char** src_suffix = NULL;
    char** dst_suffix = NULL;

    // Phase 1: Traverse Common Path
    lock(root_inum);
    
    char** common = calculate(srcpath, dstpath);
    if (common == NULL) {
        unlock(root_inum);
        goto cleanup;
    }
    
    int common_len = getlen(common);
    
    struct inode* parent = locate(root_inum, common);
    free_path(common);
    
    if (parent == NULL) {
        // locate() releases all locks when returning NULL
        goto cleanup;
    }
    
    // Phase 2: Traverse Remaining Paths
    int src_len = getlen(srcpath);
    int dst_len = getlen(dstpath);
    src_suffix_len = src_len - common_len;
    dst_suffix_len = dst_len - common_len;
    
    // Allocate and copy src suffix
    src_suffix = malloc(sizeof(char*) * (src_suffix_len + 1));
    if (src_suffix == NULL) {
        check_unlock(parent, NULL, NULL);
        goto cleanup;
    }
    for (int i = 0; i < src_suffix_len; i++) {
        src_suffix[i] = strdup(srcpath[common_len + i]);
        if (src_suffix[i] == NULL) {
            for (int j = 0; j < i; j++) {
                free(src_suffix[j]);
            }
            free(src_suffix);
            src_suffix = NULL;
            check_unlock(parent, NULL, NULL);
            goto cleanup;
        }
    }
    src_suffix[src_suffix_len] = NULL;
    
    // Allocate and copy dst suffix
    dst_suffix = malloc(sizeof(char*) * (dst_suffix_len + 1));
    if (dst_suffix == NULL) {
        for (int i = 0; i < src_suffix_len; i++) {
            free(src_suffix[i]);
        }
        free(src_suffix);
        src_suffix = NULL;
        check_unlock(parent, NULL, NULL);
        goto cleanup;
    }
    for (int i = 0; i < dst_suffix_len; i++) {
        dst_suffix[i] = strdup(dstpath[common_len + i]);
        if (dst_suffix[i] == NULL) {
            for (int j = 0; j < i; j++) {
                free(dst_suffix[j]);
            }
            free(dst_suffix);
            dst_suffix = NULL;
            for (int j = 0; j < src_suffix_len; j++) {
                free(src_suffix[j]);
            }
            free(src_suffix);
            src_suffix = NULL;
            check_unlock(parent, NULL, NULL);
            goto cleanup;
        }
    }
    dst_suffix[dst_suffix_len] = NULL;
    
    // Find srcdir from parent
    srcdir = locate_hold(parent, src_suffix);
    if (srcdir == NULL) {
        check_unlock(parent, NULL, NULL);
        goto cleanup;
    }
    
    // Find dstdir from parent
    dstdir = locate_hold(parent, dst_suffix);
    if (dstdir == NULL) {
        check_unlock(parent, srcdir, NULL);
        unlock(srcdir);
        goto cleanup;
    }
    
    // Release parent lock if different from srcdir/dstdir
    check_unlock(parent, srcdir, dstdir);
    
    // Phase 3: Checks and Operations
    if (check_src_exist_dst_delete(srcdir, dstdir, srcname, dstname) != 0) {
        goto cleanup;
    }
    
    // Perform rename operation
    struct inode* srcinode = inode_delete(srcdir, srcname);
    struct inode* dstinode = inode_delete(dstdir, dstname);
    
    if (dstinode != NULL) {
        dispose_inode(dstinode);
    }
    
    // Fixed: Use srcinode instead of srcdir
    inode_insert(dstdir, srcinode, dstname);
    
    // Release locks
    unlock2dir(srcdir, dstdir);
    
    ret = 0;

cleanup:
    if (src_suffix != NULL) {
        for (int i = 0; i < src_suffix_len; i++) {
            free(src_suffix[i]);
        }
        free(src_suffix);
    }
    if (dst_suffix != NULL) {
        for (int i = 0; i < dst_suffix_len; i++) {
            free(dst_suffix[i]);
        }
        free(dst_suffix);
    }
    
    return ret;
}