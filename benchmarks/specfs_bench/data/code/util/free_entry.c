#include "util.h"

void free_entry(struct entry* en) {
	free(en->name);
	free(en);
}