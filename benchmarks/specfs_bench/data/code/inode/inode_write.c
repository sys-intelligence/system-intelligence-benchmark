#include "inode.h"

unsigned inode_write(struct inode* node, const char* buffer, unsigned len, unsigned offset) {
    unsigned end = offset + len;

    // Calculate the new size, capped at MAX_FILE_SIZE
    if (end > MAX_FILE_SIZE) {
        end = MAX_FILE_SIZE;
    }

    // If the offset is beyond the calculated end, no bytes can be written
    if (offset >= end) {
        return 0;
    }

    unsigned new_size = end;
    unsigned written = new_size - offset;

    // If the write extends beyond the current file size, allocate and clear new space
    if (new_size > node->size) {
        unsigned alloc_start = node->size;
        unsigned alloc_len = new_size - node->size;

        file_allocate(node, alloc_start, alloc_len);
        file_clear(node, alloc_start, alloc_len);

        node->size = new_size;
    }

    // Write the data to the file
    file_write(node, offset, written, buffer);

    return written;
}