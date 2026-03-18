/*
 * The MIT License (MIT)
 *
 * Copyright (c) 2016 Hugo Guiroux <hugo.guiroux at gmail dot com>
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of his software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */
#ifndef __MCS_H__
#define __MCS_H__

#define _GNU_SOURCE

#define NUMA_NODES 2
#define CPU_NUMBER 32
#define L_CACHE_LINE_SIZE 128
#define LOCKED 0
#define UNLOCKED 1
#define SPINNING_THRESHOLD 2700LL

#define r_align(n, r) (((n) + (r) - 1) & -(r))
#define cache_align(n) r_align(n, L_CACHE_LINE_SIZE)
#define pad_to_cache_line(n) (cache_align(n) - (n))
#define MEMALIGN(ptr, alignment, size) \
	posix_memalign((void **)(ptr), (alignment), (size))

typedef struct mcs_node {
	struct mcs_node *volatile next;
	char __pad[pad_to_cache_line(sizeof(struct mcs_node *))];
	volatile int spin __attribute__((aligned(L_CACHE_LINE_SIZE)));
} mcs_node_t __attribute__((aligned(L_CACHE_LINE_SIZE)));

typedef struct mcs_mutex {
	struct mcs_node *volatile tail
		__attribute__((aligned(L_CACHE_LINE_SIZE)));
} mcs_mutex_t __attribute__((aligned(L_CACHE_LINE_SIZE)));

mcs_mutex_t *mcs_mutex_create();
int mcs_mutex_lock(mcs_mutex_t *impl, mcs_node_t *me);
void mcs_mutex_unlock(mcs_mutex_t *impl, mcs_node_t *me);
int mcs_mutex_destroy(mcs_mutex_t *lock);

typedef mcs_mutex_t lock_mutex_t;
typedef mcs_node_t lock_context_t;

#endif // __MCS_H__
