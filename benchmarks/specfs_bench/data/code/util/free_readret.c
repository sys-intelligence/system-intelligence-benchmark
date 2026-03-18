#include "util.h"

void free_readret(struct read_ret *p) {
    free(p->buf);
    free(p);
}