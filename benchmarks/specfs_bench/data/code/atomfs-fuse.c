/* * Copyright (c) 2020 Institution of Parallel and Distributed System, Shanghai Jiao Tong University
 * AtomFS is licensed under the Mulan PSL v1.
 * You can use this software according to the terms and conditions of the Mulan PSL v1.
 * You may obtain a copy of Mulan PSL v1 at:
 *     http://license.coscl.org.cn/MulanPSL
 * THIS SOFTWARE IS PROVIDED ON AN "AS IS" BASIS, WITHOUT WARRANTIES OF ANY KIND, EITHER EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO NON-INFRINGEMENT, MERCHANTABILITY OR FIT FOR A PARTICULAR
 * PURPOSE.
 * See the Mulan PSL v1 for more details.
 */

#define _GNU_SOURCE
#include "common.h"
#include "util.h"
#include "interface.h"
#include <errno.h>
#include <fuse.h>
#include <stdlib.h>
#include <unistd.h>
#include <stdio.h>
#include <stdbool.h>
#include <sys/sysmacros.h>

char *device;
char *mpoint;
bool mkfs;
struct inode *root_inum;

#define log_pmsg(fmt, ...) \
	log_msg("(%s:%d) " fmt, __func__, __LINE__, ##__VA_ARGS__)
FILE *logfile;
FILE *log_open()
{
	return NULL;
}
void log_msg(const char *format, ...)
{
}

int fs_mknod(const char *path, mode_t mode, dev_t dev)
{
	char *dirname[MAX_PATH_LEN];
	char filename[MAX_FILE_LEN];
	unsigned res;

	log_msg("\nfs_mknod(path=\"%s\", mode=0%3o, dev=%lld)\n", path, mode,
		dev);

	memset(dirname, 0, MAX_PATH_LEN * sizeof(char *));
	memset(filename, 0, MAX_FILE_LEN);
	split_dirs_file(path, dirname, filename);
	if (strlen(filename) == 0) {
		free_dirs(dirname);
		return -1;
	}
	if (S_ISREG(mode))
		res = atomfs_ins(dirname, filename, FILE_MODE, 0, 0);
	else if (S_ISSOCK(mode))
		res = atomfs_ins(dirname, filename, SOCK_MODE, 0, 0);
	else if (S_ISFIFO(mode))
		res = atomfs_ins(dirname, filename, FIFO_MODE, 0, 0);
	else if (S_ISCHR(mode))
		res = atomfs_ins(dirname, filename, CHR_MODE, major(dev),
				 minor(dev));
	else
		res = atomfs_ins(dirname, filename, BLK_MODE, major(dev),
				 minor(dev));
	free_dirs(dirname);
	return res;
}

/** Create a directory */
int fs_mkdir(const char *path, mode_t mode)
{
	char *dirname[MAX_PATH_LEN];
	char filename[MAX_FILE_LEN];
	unsigned res;

	log_msg("\nfs_mkdir(path=\"%s\", mode=0%3o)\n", path, mode);

	memset(dirname, 0, MAX_PATH_LEN * sizeof(char *));
	memset(filename, 0, MAX_FILE_LEN);
	split_dirs_file(path, dirname, filename);
	if (strlen(filename) == 0) {
		free_dirs(dirname);
		return -1;
	}
	res = atomfs_ins(dirname, filename, DIR_MODE, 0, 0);
	free_dirs(dirname);
	return res;
}

/** Remove a file */
int fs_unlink(const char *path)
{
	char *dirname[MAX_PATH_LEN];
	char filename[MAX_FILE_LEN];
	unsigned res;

	log_msg("fs_unlink(path=\"%s\")\n", path);

	if (strcmp(path, "/") == 0) {
		return -1;
	}
	memset(dirname, 0, MAX_PATH_LEN * sizeof(char *));
	memset(filename, 0, MAX_FILE_LEN);
	split_dirs_file(path, dirname, filename);
	if (strlen(filename) == 0) {
		free_dirs(dirname);
		return -1;
	}
	res = atomfs_del(dirname, filename);
	free_dirs(dirname);
	return res;
}

/** Remove a directory */
int fs_rmdir(const char *path)
{
	char *dirname[MAX_PATH_LEN];
	char filename[MAX_FILE_LEN];
	unsigned res;

	log_pmsg("(path=\"%s\")\n", path);
	if (strcmp(path, "/") == 0) {
		return -1;
	}
	memset(dirname, 0, MAX_PATH_LEN * sizeof(char *));
	memset(filename, 0, MAX_FILE_LEN);
	split_dirs_file(path, dirname, filename);
	if (strlen(filename) == 0) {
		free_dirs(dirname);
		return -1;
	}
	res = atomfs_del(dirname, filename);
	free_dirs(dirname);
	return res;
}

/** Rename a file */
int fs_rename(const char *path, const char *newpath)
{
	char *srcdir[MAX_PATH_LEN];
	char *dstdir[MAX_PATH_LEN];
	char srcname[MAX_FILE_LEN];
	char dstname[MAX_FILE_LEN];
	int res;

	log_pmsg("(fpath=\"%s\", newpath=\"%s\")\n", path, newpath);
	memset(srcdir, 0, MAX_PATH_LEN * sizeof(char *));
	memset(srcname, 0, MAX_FILE_LEN);
	memset(dstdir, 0, MAX_PATH_LEN * sizeof(char *));
	memset(dstname, 0, MAX_FILE_LEN);
	split_dirs_file(path, srcdir, srcname);
	split_dirs_file(newpath, dstdir, dstname);
	if ((strlen(srcname) == 0) || (strlen(dstname) == 0)) {
		free_dirs(srcdir);
		free_dirs(dstdir);
		return -1;
	}
	res = atomfs_rename(srcdir, dstdir, srcname, dstname);
	free_dirs(srcdir);
	free_dirs(dstdir);
	return res;
}

/** Change the size of a file */
int fs_truncate(const char *path, off_t newsize)
{
	char *dirname[MAX_PATH_LEN];
	unsigned res;

	if (newsize & 0xffffffff00000000)
		return -1;
	log_pmsg("(path=\"%s\", newsize=%lld)\n", path, newsize);
	memset(dirname, 0, MAX_PATH_LEN * sizeof(char *));
	split_dirs(path, dirname);
	res = atomfs_truncate(dirname, newsize);

	free_dirs(dirname);
	return res;
}

/** Files are accessed using path 
 * Open is not used 
 * */
int fs_open(const char *path, struct fuse_file_info *fi)
{
	char *dirname[MAX_PATH_LEN];
	struct inode *ret;

	log_pmsg("(path\"%s\", fi=0x%08x)\n", path, fi);
	memset(dirname, 0, MAX_PATH_LEN * sizeof(char *));
	split_dirs(path, dirname);
	ret = atomfs_open(dirname, FILE_MODE);
	if (ret == NULL) {
		free_dirs(dirname);
		return -1;
	}
	free_dirs(dirname);
	return 0;
}

int fs_read(const char *path, char *buf, size_t size, off_t offset,
	    struct fuse_file_info *fi)
{
	char *dirname[MAX_PATH_LEN];
	struct read_ret *res;
	unsigned temp;

	if ((size > MAX_FILE_SIZE) || ((size_t)offset > MAX_FILE_SIZE)) {
		return -1;
	}
	log_pmsg("(path=\"%s\", buf=0x%08x, size=%d, offset=%lld, fi=0x%08x)\n",
		 path, buf, size, offset, fi);
	memset(dirname, 0, MAX_PATH_LEN * sizeof(char *));
	split_dirs(path, dirname);
	res = atomfs_read(dirname, size, offset);

	free_dirs(dirname);

	if (res == NULL)
		return -1;
	if (res->num)
		memcpy(buf, res->buf, res->num);
	temp = res->num;
	free_readret(res);
	return temp;
}

int fs_write(const char *path, const char *buf, size_t size, off_t offset,
	     struct fuse_file_info *fi)
{
	char *dirname[MAX_PATH_LEN];
	int res;

	if ((size > MAX_FILE_SIZE) || ((size_t)offset > MAX_FILE_SIZE)) {
		return -1;
	}
	log_pmsg("(path=\"%s\", buf=0x%08x, size=%d, offset=%lld, fi=0x%08x)\n",
		 path, buf, size, offset, fi);
	memset(dirname, 0, MAX_PATH_LEN * sizeof(char *));
	split_dirs(path, dirname);
	res = atomfs_write(dirname, buf, size, offset);
	free_dirs(dirname);
	return res;
}

int fs_opendir(const char *path, struct fuse_file_info *fi)
{
	char *dirname[MAX_PATH_LEN];
	struct inode *ret;

	log_pmsg("fs_opendir(path=\"%s\", fi=0x%08x)\n", path, fi);
	memset(dirname, 0, MAX_PATH_LEN * sizeof(char *));
	split_dirs(path, dirname);
	ret = atomfs_open(dirname, DIR_MODE);
	if (ret == NULL) {
		free_dirs(dirname);
		return -1;
	}
	free_dirs(dirname);
	return 0;
}

int fs_readdir(const char *path, void *buf, fuse_fill_dir_t filler,
	       off_t offset, struct fuse_file_info *fi)
{
	char *dirname[MAX_PATH_LEN];
	char **dircontent;
	unsigned i = 0;

	log_pmsg(
		"(path=\"%s\", buf=0x%08x, filler=0x%08x, offset=%lld, fi=0x%08x)\n",
		path, buf, filler, offset, fi);

	memset(dirname, 0, MAX_PATH_LEN * sizeof(char *));
	split_dirs(path, dirname);
	dircontent = atomfs_readdir(dirname);
	free_dirs(dirname);
	if (dircontent == NULL) {
		return -1;
	}

	filler(buf, ".", NULL, 0);
	filler(buf, "..", NULL, 0);
	for (; dircontent[i]; ++i) {
		if (filler(buf, dircontent[i], NULL, 0) != 0) {
			for (; dircontent[i]; ++i)
				free(dircontent[i]);
			free(dircontent);
			return -ENOMEM;
		}
		free(dircontent[i]);
	}
	free(dircontent);
	return 0;
}

int fs_getattr(const char *path, struct stat *statbuf)
{
	char *dirname[MAX_PATH_LEN];
	struct getattr_ret *attr;

	log_pmsg("fs_getattr(path=\"%s\", statbuf=0x%08x)\n", path, statbuf);
	memset(dirname, 0, MAX_PATH_LEN * sizeof(char *));
	split_dirs(path, dirname);
	attr = atomfs_getattr(dirname);
	if (!attr) {
		free_dirs(dirname);
		return -ENOENT;
	}
	statbuf->st_dev = 0;
	statbuf->st_ino = (u64)(attr->inum);
	statbuf->st_uid = 0;
	statbuf->st_gid = 0;

	statbuf->st_rdev = makedev(attr->maj, attr->min);
	if (attr->mode == FILE_MODE) {
		statbuf->st_mode = 0777 | S_IFREG;
		statbuf->st_size = attr->size;
	} else if (attr->mode == DIR_MODE) {
		statbuf->st_mode = 0777 | S_IFDIR;
		statbuf->st_size = attr->size;
	} else {
		if (attr->mode == SOCK_MODE)
			statbuf->st_mode = 0777 | S_IFSOCK;
		else if (attr->mode == FIFO_MODE)
			statbuf->st_mode = 0777 | S_IFIFO;
		else if (attr->mode == CHR_MODE)
			statbuf->st_mode = 0777 | S_IFCHR;
		else
			statbuf->st_mode = 0777 | S_IFBLK;
		statbuf->st_size = 0;
	}
	statbuf->st_blksize = PAGE_SIZE;
	statbuf->st_blocks = 1;
	statbuf->st_atim.tv_sec = 0;
	statbuf->st_atim.tv_nsec = 0;
	statbuf->st_mtim.tv_sec = 0;
	statbuf->st_mtim.tv_nsec = 0;
	statbuf->st_ctim.tv_sec = 0;
	statbuf->st_ctim.tv_nsec = 0;

	free(attr);

	free_dirs(dirname);
	return 0;
}

int fs_statfs(const char *path, struct statvfs *statv)
{
	log_msg("statfs\n");
	statv->f_bsize = PAGE_SIZE; /* Filesystem block size */
	statv->f_frsize = PAGE_SIZE; /* Fragment size */
	statv->f_blocks = 0; /* Size of fs in f_frsize units */
	statv->f_bfree = 0; /* Number of free blocks */
	statv->f_bavail = 0; /* Number of free blocks for
					      unprivileged users */
	statv->f_files = 1; /* Number of inodes */
	statv->f_ffree = 10000; /* Number of free inodes */
	statv->f_favail = 10000; /* Number of free inodes for
				      unprivileged users */
	statv->f_fsid = 0x50F5; /* Filesystem ID */
	statv->f_flag = 0; /* Mount flags */
	statv->f_namemax = 39; /* Maximum filename length */
	return 0;
}

int fs_readlink(const char *path, char *link, size_t size)
{
	log_msg("read_link\n");
	return 0;
}

void *fs_init(struct fuse_conn_info *conn)
{
	log_msg("\nfs_init()\n");
	return FS_DATA;
}

void fs_destroy(void *userdata)
{
	log_msg("fs_destroy(userdata=0x%08x)\n", userdata);
	return;
}

int fs_symlink(const char *path, const char *link)
{
	log_msg("sym_link\n");
	return -ENOSYS;
}

int fs_link(const char *path, const char *newpath)
{
	log_msg("link\n");
	return -ENOSYS;
}

int fs_chmod(const char *path, mode_t mode)
{
	log_msg("chmod\n");
	return 0;
}

int fs_chown(const char *path, uid_t uid, gid_t gid)
{
	log_msg("chown\n");
	return 0;
}

int fs_utimens(const char *path, const struct timespec tv[2])
{
	log_msg("utime\n");
	return 0;
}

int fs_flush(const char *path, struct fuse_file_info *fi)
{
	log_msg("flush\n");
	return 0;
}

int fs_release(const char *path, struct fuse_file_info *fi)
{
	log_msg("release\n");
	return 0;
}

int fs_releasedir(const char *path, struct fuse_file_info *fi)
{
	log_msg("releasedir\n");
	return 0;
}

int fs_access(const char *path, int mask)
{
	log_msg("access\n");
	return 0;
}

int fs_fsyncdir(const char *path, int datasync, struct fuse_file_info *fi)
{
	log_msg("(path=\"%s\", datasync=%d, fi=0x%08x)\n", path, datasync, fi);
	return 0;
}

int fs_fsync(const char *path, int datasync, struct fuse_file_info *fi)
{
	log_msg("(path=\"%s\", datasync=%d, fi=0x%08x)\n", path, datasync, fi);
	return 0;
}

struct fuse_operations fs_oper = {
	.getattr = fs_getattr,
	.readlink = fs_readlink,

	.getdir = NULL,
	.mknod = fs_mknod,
	.mkdir = fs_mkdir,
	.unlink = fs_unlink,
	.rmdir = fs_rmdir,
	.symlink = fs_symlink,
	.rename = fs_rename,
	.link = fs_link,
	.chmod = fs_chmod,
	.chown = fs_chown,
	.truncate = fs_truncate,
	.utimens = fs_utimens,
	.open = fs_open,
	.read = fs_read,
	.write = fs_write,
	.statfs = fs_statfs,
	.flush = fs_flush,
	.release = fs_release,
	.fsync = fs_fsync,
	.opendir = fs_opendir,
	.readdir = fs_readdir,
	.releasedir = fs_releasedir,
	.fsyncdir = fs_fsyncdir,
	.init = fs_init,
	.destroy = fs_destroy,
	.access = fs_access,
	.ftruncate = NULL,
};

void parse_opts(int argc, char *argv[])
{
	int opt;
	bool init = false;
	while ((opt = getopt(argc, argv, "n")) != -1) {
		switch (opt) {
		case 'n':
			init = true;
			break;
		default:
			fprintf(stderr, "Usage: %s [-n] device mountPoint\n",
				argv[0]);
			fprintf(stderr, "   option: -n, make a new fs\n");
			abort();
		}
	}
	if (optind + 1 >= argc) {
		fprintf(stderr, "Expect device and mount point!\n");
		abort();
	}

	device = argv[optind];
	mpoint = argv[optind + 1];
	mkfs = init;
}

int main(int argc, char *argv[])
{
	int fuse_stat;
	struct fs_state *fs_data = NULL;
	if ((getuid() == 0) || (geteuid() == 0)) {
		fprintf(stderr,
			"Running AtomFS as root opens unnacceptable security holes\n");
		return 1;
	}

	// See which version of fuse we're running
	fprintf(stderr, "Fuse library version %d.%d\n", FUSE_MAJOR_VERSION,
		FUSE_MINOR_VERSION);

	parse_opts(argc, argv);

	printf("atomfs: mount device '%s' at '%s'\n", device, mpoint);

	fs_data = malloc(sizeof(struct fs_state));
	if (fs_data == NULL) {
		perror("main calloc");
		abort();
	}

	fs_data->logfile = log_open();

	argc--;
	argv[1] = argv[2];
	argv[2] = argv[3];
	argc--;
	argv[1] = argv[2];

	//added by atomfs
	root_inum = malloc_inode(DIR_MODE, 0, 0);
	struct fuse_args args = FUSE_ARGS_INIT(0, NULL);
	fuse_opt_add_arg(&args, argv[0]);
#ifdef DEBUG
	fuse_opt_add_arg(&args, "-d");
	fuse_opt_add_arg(&args, "-odebug");
#endif
	fuse_opt_add_arg(&args, "-f");
	fuse_opt_add_arg(&args, argv[1]);

	fuse_opt_add_arg(&args, "-oallow_root");

	printf("args.argc= %d\n", args.argc);
	int i;
	for (i = 0; i < args.argc; ++i)
		printf("args.argv[%d] = %s\n", i, args.argv[i]);

	// turn over control to fuse
	fprintf(stderr, "about to call fuse_main\n");
	fuse_stat = fuse_main(args.argc, args.argv, &fs_oper, fs_data);
	fprintf(stderr, "fuse_main returned %d\n", fuse_stat);

	return fuse_stat;
}
