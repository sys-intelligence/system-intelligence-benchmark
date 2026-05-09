#include "util.h"

unsigned int hash_name(char* name) {
    unsigned int hash = 0;

    if (name == NULL) {
        return 0;
    }

    while (*name != '\0') {
        hash = (hash * 131) + *name;
        name++;
    }

    return hash & 0x1ff;
}