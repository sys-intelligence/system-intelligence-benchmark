#ifndef _COMMON_H
#define _COMMON_H

#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/syscall.h>
#include <assert.h>


#define FUSE_USE_VERSION 26
#define FS_DATA ((struct fs_state *)fuse_get_context()->private_data)
#define LOCK_COUPLING

#define FILE_MODE 1
#define DIR_MODE 2
#define CHR_MODE 3
#define BLK_MODE 4
#define SOCK_MODE 5
#define FIFO_MODE 6

#define PG_SIZE 4096
#define INDEXTB_NUM 8192
#define DIRTB_NUM 512
#define MAX_FILE_LEN 256
#define MAX_DIR_SIZE 10000000
#define MAX_PATH_LEN 100
#define MAX_FILE_SIZE ((unsigned)(INDEXTB_NUM * PG_SIZE))
#define PAGE_SIZE (4096)

typedef unsigned long long u64;
typedef struct entry {
	char *name;
	void *inum;
	struct entry *next;
} entry;

typedef struct indextb {
	unsigned char *index[INDEXTB_NUM];
} indextb;

typedef struct dirtb {
	struct entry *tb[DIRTB_NUM];
} dirtb;

typedef struct inode {
	int mutex;
	struct mcs_mutex *impl;
	struct mcs_node *hd;
	unsigned maj;
	unsigned min;
	unsigned int mode;
	unsigned int size;
	struct dirtb *dir;
	struct indextb *file;
} inode;

typedef struct getattr_ret {
	struct inode *inum;
	unsigned mode;
	unsigned size;
	unsigned maj;
	unsigned min;
} getattr_ret;

typedef struct read_ret {
	char *buf;
	unsigned num;
} read_ret;

extern struct inode *root_inum;

struct fs_state {
	FILE *logfile;
};
#endif // _COMMON_H