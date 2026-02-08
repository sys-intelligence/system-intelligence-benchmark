#!/bin/bash
set -euo pipefail

# Reference solution script: write a correct allocator, build, and run traces.
cat > mm.c << 'EOF'
/*
 * Reference solution for the CS:APP malloc lab.
 *
 * Implicit free list with boundary tags, first-fit placement, and
 * immediate coalescing.
 */
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * Team information
 ********************************************************/
team_t team = {
	"reference",
	"Reference Solution",
	"reference@local",
	"",
	""
};

/* Basic constants and macros */
#define WSIZE 4             /* word size (bytes) */
#define DSIZE 8             /* double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* initial heap size (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and prev blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *heap_listp = NULL;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

int mm_init(void)
{
	if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) {
		return -1;
	}
	PUT(heap_listp, 0);
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));
	heap_listp += (2 * WSIZE);

	if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
		return -1;
	}
	return 0;
}

void *mm_malloc(size_t size)
{
	size_t asize;
	size_t extendsize;
	char *bp;

	if (size == 0) {
		return NULL;
	}

	if (size <= DSIZE) {
		asize = 2 * DSIZE;
	} else {
		asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
	}

	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
	}

	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
		return NULL;
	}
	place(bp, asize);
	return bp;
}

void mm_free(void *ptr)
{
	if (ptr == NULL) {
		return;
	}
	size_t size = GET_SIZE(HDRP(ptr));

	PUT(HDRP(ptr), PACK(size, 0));
	PUT(FTRP(ptr), PACK(size, 0));
	coalesce(ptr);
}

void *mm_realloc(void *ptr, size_t size)
{
	if (ptr == NULL) {
		return mm_malloc(size);
	}
	if (size == 0) {
		mm_free(ptr);
		return NULL;
	}

	void *newptr = mm_malloc(size);
	if (newptr == NULL) {
		return NULL;
	}

	size_t copy_size = GET_SIZE(HDRP(ptr)) - DSIZE;
	if (size < copy_size) {
		copy_size = size;
	}
	memcpy(newptr, ptr, copy_size);
	mm_free(ptr);
	return newptr;
}

static void *extend_heap(size_t words)
{
	char *bp;
	size_t size;

	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((long)(bp = mem_sbrk(size)) == -1) {
		return NULL;
	}

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

	return coalesce(bp);
}

static void *coalesce(void *bp)
{
	size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	size_t size = GET_SIZE(HDRP(bp));

	if (prev_alloc && next_alloc) {
		return bp;
	} else if (prev_alloc && !next_alloc) {
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
	} else if (!prev_alloc && next_alloc) {
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	} else {
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		bp = PREV_BLKP(bp);
	}
	return bp;
}

static void *find_fit(size_t asize)
{
	void *bp;

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
			return bp;
		}
	}
	return NULL;
}

static void place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));

	if ((csize - asize) >= (2 * DSIZE)) {
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
	}
}
EOF

make clean > /dev/null 2>&1 || true
make > /dev/null 2>&1

./mdriver -f short1-bal.rep > /dev/null 2>&1
./mdriver -f short2-bal.rep > /dev/null 2>&1

echo "PASS: reference solution completed"
