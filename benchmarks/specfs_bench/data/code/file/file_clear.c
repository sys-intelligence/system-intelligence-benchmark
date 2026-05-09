#include "file.h"

void file_clear(struct inode *node, unsigned start, unsigned len) {
    // According to [RELY], file_write writes zeroes if data is NULL.
    // We utilize this behavior to clear the specified range.
    file_write(node, start, len, NULL);
}