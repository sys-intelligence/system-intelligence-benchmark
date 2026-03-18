#ifndef _INTERFACE_H
#define _INTERFACE_H

#include "common.h"
#include "util.h"
#include "inode.h"
#include "interface-util.h"
#include "path.h"

struct inode *atomfs_open(char *path[], unsigned mode);
int atomfs_truncate(char* path[], unsigned offset);
int atomfs_rename(char* srcpath[], char* dstpath[], char* srcname, char* dstname);
char **atomfs_readdir(char *path[]);
struct read_ret* atomfs_read(char* path[], unsigned size, unsigned offset);
int atomfs_ins(char* path[], char* name, int mode, unsigned maj, unsigned min);
int atomfs_del(char* path[], char* name);
struct getattr_ret* atomfs_getattr(char* path[]);
int atomfs_write(char* path[], const char* buf, unsigned size, unsigned offset);
#endif // _INTERFACE_H