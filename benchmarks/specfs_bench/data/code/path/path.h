#ifndef _PATH_H
#define _PATH_H

#include "inode.h"
#include "common.h"
#include "util.h"

struct inode* locate(struct inode* cur, char* path[]);
struct inode* locate_hold(struct inode *cur, char *path[]);
#endif // _PATH_H