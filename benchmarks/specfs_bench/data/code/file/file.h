#ifndef _FILE_H
#define _FILE_H

#include "common.h"
#include "util.h"

void file_clear(struct inode *node, unsigned start, unsigned len);
void file_allocate(struct inode *node, unsigned offset, unsigned len);
void file_read(struct inode *node, unsigned offset, unsigned len, char *data);
void file_write(struct inode *node, unsigned offset, unsigned len, const char *data);
#endif // _FILE_H