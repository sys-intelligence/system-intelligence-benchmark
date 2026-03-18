/*
 * The MIT License (MIT)
 *
 * Copyright (c) 2016 Hugo Guiroux <hugo.guiroux at gmail dot com>
 *               UPMC, 2010-2011, Jean-Pierre Lozi <jean-pierre.lozi@lip6.fr>
 *                                Gaël Thomas <gael.thomas@lip6.fr>
 *                                Florian David <florian.david@lip6.fr>
 *                                Julia Lawall <julia.lawall@lip6.fr>
 *                                Gilles Muller <gilles.muller@lip6.fr>
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
 *
 *
 * John M. Mellor-Crummey and Michael L. Scott. 1991.
 * Algorithms for scalable synchronization on shared-memory multiprocessors.
 * ACM Trans. Comput. Syst. 9, 1 (February 1991).
 *
 * Lock design summary:
 * The MCS lock is one of the most known multicore locks.
 * Its main goal is to avoid all threads spinning on the same memory address as
 * it induces contention due to the cache coherency protocol.
 * The lock is organized as a FIFO list: this ensures total fairness.
 * Each thread as its own context, which is a node that the thread will put into
 * the linked list (representing the list of threads waiting for the lock) when
 * it tries to grab the lock.
 * The lock is a linked-list composed of a pointer to the tail of the list.
 * - On lock: the thread does an atomic xchg to put itself to the end of the
 * linked list and get the previous tail of the list.
 *   If there was no other thread waiting, then the thread has the lock.
 * Otherwise, the thread spins on a memory address contained in its context.
 * - On unlock: if there is any thread, we just wake the next thread on the
 * waiting list. Otherwise we set the tail of the queue to NULL.
 */

/*
 * [Module Name] MCS
 * [Rely] None
 */

#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>
#include <sys/mman.h>
#include <pthread.h>
#include <assert.h>
#include "mcs.h"

#define CPU_PAUSE() asm volatile("pause\n")
#define COMPILER_BARRIER() asm volatile("" : : : "memory")

static inline void *xchg_64(void *ptr, void *x)
{
	__asm__ __volatile__("xchgq %0,%1"
			     : "=r"((unsigned long long)x)
			     : "m"(*(volatile long long *)ptr),
			       "0"((unsigned long long)x)
			     : "memory");

	return x;
}

static inline void *alloc_cache_align(size_t n)
{
	void *res = 0;
	if ((MEMALIGN(&res, L_CACHE_LINE_SIZE, cache_align(n)) < 0) || !res) {
		fprintf(stderr, "MEMALIGN(%llu, %llu)", (unsigned long long)n,
			(unsigned long long)cache_align(n));
		exit(-1);
	}
	return res;
}

static inline void waiting_policy_sleep(volatile int *var)
{
	while (!(*var)) {
		CPU_PAUSE();
	}
}

static inline void waiting_policy_wake(volatile int *var)
{
	*var = UNLOCKED;
	//assert(old == 0);
}

mcs_mutex_t *mcs_mutex_create()
{
	mcs_mutex_t *impl =
		(mcs_mutex_t *)alloc_cache_align(sizeof(mcs_mutex_t));
	impl->tail = 0;
	return impl;
}

static int __mcs_mutex_lock(mcs_mutex_t *impl, mcs_node_t *me)
{
	mcs_node_t *tail;

	//assert(me != NULL);

	me->next = LOCKED;
	me->spin = 0;

	// The atomic instruction is needed when two threads try to put themselves
	// at the tail of the list at the same time
	tail = xchg_64((void *)&impl->tail, (void *)me);

	/* No one there? */
	if (!tail) {
		return 0;
	}

	/* Someone there, need to link in */
	tail->next = me;
	COMPILER_BARRIER();

	//waiting_policy_sleep(&me->spin);
	while (!me->spin) {
		CPU_PAUSE();
	}

	return 0;
}

int mcs_mutex_lock(mcs_mutex_t *impl, mcs_node_t *me)
{
	int ret = __mcs_mutex_lock(impl, me);
	//assert(ret == 0);
	//DEBUG("[%d] Lock acquired posix=%p\n", cur_thread_id, &impl->posix_lock);
	return ret;
}

static void __mcs_mutex_unlock(mcs_mutex_t *impl, mcs_node_t *me)
{
	/* No successor yet? */
	if (!me->next) {
		// The atomic instruction is needed if a thread between the previous if
		// and now has enqueued itself at the tail
		if (__sync_val_compare_and_swap(&impl->tail, me, 0) == me)
			return;

		/* Wait for successor to appear */
		while (!me->next) {
			CPU_PAUSE();
		}
	}

	/* Unlock next one */
	//waiting_policy_wake(&me->next->spin);
	me->next->spin = UNLOCKED;
}

void mcs_mutex_unlock(mcs_mutex_t *impl, mcs_node_t *me)
{
	__mcs_mutex_unlock(impl, me);
}

int mcs_mutex_destroy(mcs_mutex_t *lock)
{
	free(lock);
	lock = NULL;

	return 0;
}
