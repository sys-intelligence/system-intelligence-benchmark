#include "file.h"

void file_write(struct inode *node, unsigned offset, unsigned len, const char *data) {
    if (len == 0 || node == NULL || node->file == NULL) {
        return;
    }

    struct indextb *tb = node->file;
    unsigned current_offset = offset;
    unsigned remaining = len;
    unsigned data_idx = 0;

    while (remaining > 0) {
        unsigned page_idx = current_offset / PAGE_SIZE;
        unsigned page_offset = current_offset % PAGE_SIZE;
        unsigned bytes_in_page = PAGE_SIZE - page_offset;
        unsigned bytes_to_write = (remaining < bytes_in_page) ? remaining : bytes_in_page;

        unsigned char *page = tb->index[page_idx];

        if (data != NULL) {
            for (unsigned i = 0; i < bytes_to_write; i++) {
                page[page_offset + i] = data[data_idx + i];
            }
        } else {
            for (unsigned i = 0; i < bytes_to_write; i++) {
                page[page_offset + i] = 0;
            }
        }

        current_offset += bytes_to_write;
        remaining -= bytes_to_write;
        data_idx += bytes_to_write;
    }
}