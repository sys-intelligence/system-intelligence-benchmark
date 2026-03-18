#include "util.h"

int getlen(char* path[]) {
    int count = 0;
    while (path[count] != NULL) {
        count++;
    }
    return count;
}