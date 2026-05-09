#include "inode.h"

struct inode *inode_find(struct inode *node, char *name) {
    unsigned int n = hash_name(name);
    struct entry *curr = node->dir->tb[n];

    while (curr != NULL) {
        if (strcmp(curr->name, name) == 0) {
            return (struct inode *)curr->inum;
        }
        curr = curr->next;
    }

    return NULL;
}