#include "util.h"

struct entry *malloc_entry() {
    return malloc(sizeof(struct entry));
}