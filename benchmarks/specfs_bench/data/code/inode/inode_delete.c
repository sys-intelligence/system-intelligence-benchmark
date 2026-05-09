#include "inode.h"

struct inode* inode_delete(struct inode* inum, char* name) {
    unsigned int n = hash_name(name);
    struct entry *prev = NULL;
    struct entry *curr = inum->dir->tb[n];
    
    while (curr != NULL) {
        if (strcmp(curr->name, name) == 0) {
            struct inode* ret_inum = curr->inum;
            
            if (prev == NULL) {
                inum->dir->tb[n] = curr->next;
            } else {
                prev->next = curr->next;
            }
            
            free_entry(curr);
            inum->size--;
            
            return ret_inum;
        }
        prev = curr;
        curr = curr->next;
    }
    
    return NULL;
}