#include "inode.h"

int inode_insert(struct inode* cur, struct inode* inum, char* name) {
    unsigned int n = hash_name(name);
    struct entry *new_entry = malloc_entry();

    if (new_entry == NULL) {
        return 1;
    }

    char *new_name = malloc_string(name);
    if (new_name == NULL) {
        free(new_entry);
        return 1;
    }

    new_entry->name = new_name;
    new_entry->inum = inum;
    new_entry->next = cur->dir->tb[n];

    cur->dir->tb[n] = new_entry;
    cur->size++;

    return 0;
}