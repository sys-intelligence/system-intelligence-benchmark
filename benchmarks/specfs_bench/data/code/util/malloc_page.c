#include "util.h"

unsigned char* malloc_page() {
    return (unsigned char*)calloc(1, PAGE_SIZE);
}