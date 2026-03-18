#ifndef _INODE_H
#define _INODE_H

#include "common.h"
#include "util.h"
#include "file.h"

int inode_insert(struct inode* cur, struct inode* inum, char* name);
struct inode* inode_delete(struct inode* inum, char* name);
unsigned inode_write(struct inode* node, const char* buffer, unsigned len, unsigned offset);
void inode_truncate(struct inode* node, unsigned size);
struct read_ret* inode_read(struct inode* node, unsigned len, unsigned offset);
struct inode *inode_find(struct inode *node, char *name);
#endif // _INODE_H