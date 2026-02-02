#!/bin/bash
set -e

# Reference solution for CS537 File System Checker

cd /workspace/ostep-projects/filesystems-checker && cat > xcheck.c << 'EOF'
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/stat.h>

#include "types.h"
#include "fs.h"

#define T_DIR  1   // Directory
#define T_FILE 2   // File
#define T_DEV  3   // Device

void *img_ptr;
struct superblock *sb;
struct dinode *inodes;
uint *bitmap;
uint nblocks_total;
uint data_block_start;

// Helper function to get inode by number
struct dinode *get_inode(uint inum) {
    uint block = IBLOCK(inum, (*sb));
    uint offset = inum % IPB;
    char *block_ptr = (char *)img_ptr + block * BSIZE;
    return &((struct dinode *)block_ptr)[offset];
}

// Helper to check if a bit is set in bitmap
int bitmap_is_set(uint block) {
    uint byte_offset = block / 8;
    uint bit_offset = block % 8;
    uchar *bmap = (uchar *)bitmap;
    return (bmap[byte_offset] & (1 << bit_offset)) != 0;
}

void error_exit(const char *msg) {
    fprintf(stderr, "%s\n", msg);
    exit(1);
}

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: xcheck <file_system_image>\n");
        exit(1);
    }
    
    int fd = open(argv[1], O_RDONLY);
    if (fd < 0) {
        fprintf(stderr, "image not found.\n");
        exit(1);
    }
    
    struct stat st;
    fstat(fd, &st);
    
    img_ptr = mmap(NULL, st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
    if (img_ptr == MAP_FAILED) {
        fprintf(stderr, "mmap failed.\n");
        exit(1);
    }
    
    // Read superblock
    sb = (struct superblock *)((char *)img_ptr + BSIZE);
    nblocks_total = sb->size;
    
    // Get bitmap location
    bitmap = (uint *)((char *)img_ptr + sb->bmapstart * BSIZE);
    
    // Calculate where data blocks start
    // Data blocks come after: boot (1) + super (1) + log + inodes + bitmap
    uint nbitmap = (nblocks_total / (BSIZE * 8)) + 1;
    data_block_start = sb->bmapstart + nbitmap;
    
    // Track used blocks and inodes
    int *block_usage = calloc(nblocks_total, sizeof(int));
    int *inode_refs = calloc(sb->ninodes, sizeof(int));
    int *dir_refs = calloc(sb->ninodes, sizeof(int));
    
    // Check 1: Each inode is either unallocated or one of valid types
    for (uint i = 0; i < sb->ninodes; i++) {
        struct dinode *inode = get_inode(i);
        if (inode->type != 0 && inode->type != T_FILE && 
            inode->type != T_DIR && inode->type != T_DEV) {
            error_exit("ERROR: bad inode.");
        }
    }
    
    // Check 2: For in-use inodes, each address is valid
    // Check 5: Each address in use is marked in bitmap
    // Check 7 & 8: Each address is only used once
    for (uint i = 0; i < sb->ninodes; i++) {
        struct dinode *inode = get_inode(i);
        if (inode->type == 0) continue;
        
        // Check direct blocks
        for (int j = 0; j < NDIRECT; j++) {
            uint addr = inode->addrs[j];
            if (addr == 0) continue;
            
            // Check 2: valid address (should be in data block region)
            if (addr < data_block_start || addr >= nblocks_total) {
                error_exit("ERROR: bad direct address in inode.");
            }
            
            // Check 5: marked in bitmap
            if (!bitmap_is_set(addr)) {
                error_exit("ERROR: address used by inode but marked free in bitmap.");
            }
            
            // Check 7: used only once
            block_usage[addr]++;
            if (block_usage[addr] > 1) {
                error_exit("ERROR: direct address used more than once.");
            }
        }
        
        // Check indirect block
        uint indirect_addr = inode->addrs[NDIRECT];
        if (indirect_addr != 0) {
            // Check 2: valid indirect block address
            if (indirect_addr < data_block_start || indirect_addr >= nblocks_total) {
                error_exit("ERROR: bad indirect address in inode.");
            }
            
            // Check 5: indirect block marked in bitmap
            if (!bitmap_is_set(indirect_addr)) {
                error_exit("ERROR: address used by inode but marked free in bitmap.");
            }
            
            // Check 8: indirect block used only once
            block_usage[indirect_addr]++;
            if (block_usage[indirect_addr] > 1) {
                error_exit("ERROR: indirect address used more than once.");
            }
            
            // Check addresses within indirect block
            uint *indirect = (uint *)((char *)img_ptr + indirect_addr * BSIZE);
            for (int j = 0; j < NINDIRECT; j++) {
                uint addr = indirect[j];
                if (addr == 0) continue;
                
                // Check 2: valid address
                if (addr < data_block_start || addr >= nblocks_total) {
                    error_exit("ERROR: bad indirect address in inode.");
                }
                
                // Check 5: marked in bitmap
                if (!bitmap_is_set(addr)) {
                    error_exit("ERROR: address used by inode but marked free in bitmap.");
                }
                
                // Check 8: used only once
                block_usage[addr]++;
                if (block_usage[addr] > 1) {
                    error_exit("ERROR: indirect address used more than once.");
                }
            }
        }
    }
    
    // Check 3: Root directory exists, inode 1, parent is itself
    struct dinode *root = get_inode(ROOTINO);
    if (root->type != T_DIR) {
        error_exit("ERROR: root directory does not exist.");
    }
    
    // Check root's .. entry
    int root_parent_ok = 0;
    uint size = root->size;
    uint nentries = size / sizeof(struct dirent);
    for (uint i = 0; i < nentries; i++) {
        uint block_index = (i * sizeof(struct dirent)) / BSIZE;
        uint offset_in_block = (i * sizeof(struct dirent)) % BSIZE;
        uint block_addr = root->addrs[block_index];
        
        struct dirent *de = (struct dirent *)((char *)img_ptr + block_addr * BSIZE + offset_in_block);
        if (de->inum != 0 && strcmp(de->name, "..") == 0) {
            if (de->inum == ROOTINO) {
                root_parent_ok = 1;
            }
            break;
        }
    }
    if (!root_parent_ok) {
        error_exit("ERROR: root directory does not exist.");
    }
    
    // Check 4: Each directory contains . and .. entries, . points to itself
    for (uint i = 0; i < sb->ninodes; i++) {
        struct dinode *inode = get_inode(i);
        if (inode->type != T_DIR) continue;
        
        int has_dot = 0, has_dotdot = 0, dot_correct = 0;
        uint size = inode->size;
        uint nentries = size / sizeof(struct dirent);
        
        for (uint j = 0; j < nentries; j++) {
            uint block_index = (j * sizeof(struct dirent)) / BSIZE;
            uint offset_in_block = (j * sizeof(struct dirent)) % BSIZE;
            uint block_addr;
            
            if (block_index < NDIRECT) {
                block_addr = inode->addrs[block_index];
            } else {
                uint *indirect = (uint *)((char *)img_ptr + inode->addrs[NDIRECT] * BSIZE);
                block_addr = indirect[block_index - NDIRECT];
            }
            
            struct dirent *de = (struct dirent *)((char *)img_ptr + block_addr * BSIZE + offset_in_block);
            
            if (de->inum != 0) {
                if (strcmp(de->name, ".") == 0) {
                    has_dot = 1;
                    if (de->inum == i) {
                        dot_correct = 1;
                    }
                }
                if (strcmp(de->name, "..") == 0) {
                    has_dotdot = 1;
                }
            }
        }
        
        if (!has_dot || !has_dotdot || !dot_correct) {
            error_exit("ERROR: directory not properly formatted.");
        }
    }
    
    // Check 9, 10, 11, 12: Count references to inodes from directories
    for (uint i = 0; i < sb->ninodes; i++) {
        struct dinode *inode = get_inode(i);
        if (inode->type != T_DIR) continue;
        
        uint size = inode->size;
        uint nentries = size / sizeof(struct dirent);
        
        for (uint j = 0; j < nentries; j++) {
            uint block_index = (j * sizeof(struct dirent)) / BSIZE;
            uint offset_in_block = (j * sizeof(struct dirent)) % BSIZE;
            uint block_addr;
            
            if (block_index < NDIRECT) {
                block_addr = inode->addrs[block_index];
            } else {
                uint *indirect = (uint *)((char *)img_ptr + inode->addrs[NDIRECT] * BSIZE);
                block_addr = indirect[block_index - NDIRECT];
            }
            
            struct dirent *de = (struct dirent *)((char *)img_ptr + block_addr * BSIZE + offset_in_block);
            
            if (de->inum != 0) {
                // Check 10: inode referred to in directory is marked in use
                struct dinode *ref_inode = get_inode(de->inum);
                if (ref_inode->type == 0) {
                    error_exit("ERROR: inode referred to in directory but marked free.");
                }
                
                // Count references
                // For directories: skip .. entries since they point to parent
                // For all: skip . entries since they are self-references
                if (strcmp(de->name, ".") != 0 && strcmp(de->name, "..") != 0) {
                    inode_refs[de->inum]++;
                    
                    // Check 12: directories should only appear once
                    if (ref_inode->type == T_DIR) {
                        dir_refs[de->inum]++;
                        if (dir_refs[de->inum] > 1) {
                            error_exit("ERROR: directory appears more than once in file system.");
                        }
                    }
                } else if (strcmp(de->name, ".") == 0) {
                    // Count . references for all directories (including root)
                    inode_refs[de->inum]++;
                }
            }
        }
    }
    
    // Check 9: All in-use inodes must be referenced in a directory
    for (uint i = 1; i < sb->ninodes; i++) {
        struct dinode *inode = get_inode(i);
        if (inode->type != 0 && inode_refs[i] == 0) {
            error_exit("ERROR: inode marked use but not found in a directory.");
        }
    }
    
    // Check 11: Reference counts match
    for (uint i = 0; i < sb->ninodes; i++) {
        struct dinode *inode = get_inode(i);
        if (inode->type == T_FILE || inode->type == T_DEV) {
            if (inode->nlink != inode_refs[i]) {
                error_exit("ERROR: bad reference count for file.");
            }
        }
    }
    
    // Check 6: Bitmap marks block in use but it's not in use
    // Only check data blocks (blocks that could be allocated to files)
    for (uint i = data_block_start; i < nblocks_total; i++) {
        if (bitmap_is_set(i) && block_usage[i] == 0) {
            error_exit("ERROR: bitmap marks block in use but it is not in use.");
        }
    }
    
    free(block_usage);
    free(inode_refs);
    free(dir_refs);
    munmap(img_ptr, st.st_size);
    close(fd);
    
    return 0;
}
EOF
