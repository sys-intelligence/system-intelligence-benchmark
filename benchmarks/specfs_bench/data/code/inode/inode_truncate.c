#include "inode.h"

void inode_truncate(struct inode* node, unsigned size) {
    if (size < node->size) {
        file_clear(node, size, node->size - size);
        node->size = size;
    } else if (size > node->size) {
        unsigned diff = size - node->size;
        file_allocate(node, node->size, diff);
        file_clear(node, node->size, diff);
        node->size = size;
    }
}