#ifndef _UTIL_H
#define _UTIL_H

#include <stdlib.h>
#include "common.h"
#include "mcs.h"

unsigned char* malloc_page();
char** malloc_dir_content(unsigned size);
char* malloc_buffer(unsigned len);
struct read_ret* malloc_readret();
void fill_dir(struct inode* inum, char** dircontent);
void free_dirs(char *dirname[]);
struct inode* malloc_inode(int mode, unsigned maj, unsigned min);
char** calculate(char* srcpath[], char* dstpath[]);
void free_path(char** path);
int getlen(char* path[]);
void lock(struct inode* inum);
void unlock2dir (struct inode* srcdir, struct inode* dstdir);
void unlock(struct inode* inum);
void dispose_inode(struct inode* inum);
char** malloc_path(unsigned len);
void free_readret(struct read_ret *p);
struct entry *malloc_entry();
void split_dirs_file(const char *path, char *dirname[], char *filename);
void split_dirs(const char *path, char *dirname[]);
unsigned int hash_name(char* name);
char* malloc_string(const char* name);
void free_entry(struct entry* en);
struct getattr_ret* malloc_getattr_ret(struct inode* inum, unsigned mode, unsigned size, unsigned maj, unsigned min);
#endif // _UTIL_H