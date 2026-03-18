#ifndef _INTERFACE_UTIL_H
#define _INTERFACE_UTIL_H

#include "inode.h"
#include "common.h"
#include "util.h"

int check_file(struct inode *inum);
void check_unlock (struct inode* parent, struct inode* src, struct inode* dst);
int check_ins(struct inode *cur, char *name);
int check_dir(struct inode *inum);
int check_src_exist_dst_delete(struct inode *srcdir, struct inode *dstdir, char *srcname, char *dstname);
int check_del(struct inode *cur, char *name);
int check_open(struct inode *inum, unsigned mode);
#endif // _INTERFACE_UTIL_H