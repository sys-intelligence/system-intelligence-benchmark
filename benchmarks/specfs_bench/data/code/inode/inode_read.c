#include "inode.h"

struct read_ret* inode_read(struct inode* node, unsigned len, unsigned offset) {
    struct read_ret* ret = malloc_readret();

    if (offset >= node->size || len == 0) {
        ret->num = 0;
        ret->buf = NULL;
        return ret;
    }

    unsigned remaining = node->size - offset;
    unsigned actual_len = (len < remaining) ? len : remaining;

    char* buf = malloc_buffer(actual_len);
    file_read(node, offset, actual_len, buf);

    ret->buf = buf;
    ret->num = actual_len;

    return ret;
}