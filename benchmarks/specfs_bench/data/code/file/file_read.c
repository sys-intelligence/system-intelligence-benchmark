#include "file.h"

void file_read(struct inode *node, unsigned offset, unsigned len, char *data) {
    unsigned current_offset = offset;
    unsigned remaining = len;
    char *dst = data;

    while (remaining > 0) {
        unsigned page_idx = current_offset >> 12;
        unsigned page_offset = current_offset & 0xFFF;
        unsigned char *page_ptr = node->file->index[page_idx];

        unsigned bytes_in_page = PG_SIZE - page_offset;
        unsigned to_copy = (remaining < bytes_in_page) ? remaining : bytes_in_page;

        memcpy(dst, page_ptr + page_offset, to_copy);

        dst += to_copy;
        current_offset += to_copy;
        remaining -= to_copy;
    }
}