/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include "mm.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Kim Seonghoon",
    /* First member's email address */
    "ggu1012@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

void *extend_heap(size_t size);
void *coalesce(void *bp);
void place(void *bp, int alloc_size);

/* Macros below are based on the textbook example
 * on page 893.
 */

/* Basic constants and macros */
#define WSIZE 4     /* Word and header/footer size (bytes) */
#define DSIZE 8     /* Double word size (bytes) */
#define MIN_SIZE 16 /* Minimum size to contain two pointers and header + footer for free blocks */

#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks in the address insight*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

#define ALIGNMENT 8
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

/* Find out the next node of free block in the level insight.
 * Prev node = bp
 */
#define NEXT_NODE(bp) ((char *)(bp) + WSIZE)

static char *lv_header;    // Pointing Lv1. header
static char *storage = 0;  // Region after level headers. Storing starts here.
static char *heap_end;

void *lv_root(int level) {
    /* returns the address of level root */
    return lv_header + (level - 1) * 4;
}

// Level 1 : size 0 ~ 2^8-1
// Level 2 : size 2^8 ~ 2^16-1
// Level 3 : size 2^16 ~ 2^24-1
// Level 4 : 2^24 ~ 2^32-1
size_t size_level(size_t size) {
    int n = 0;
    int div = 0;
    while (size > (div = 1 << (n << 3))) {
        n++;
        if (n == 3) break;
    }
    return n++;
}

/* Insert node in level list after root */
void insert_node(int level, void *bp) {
    char *bp_next = NEXT_NODE(bp);
    char *original_root_next = GET(lv_root(level));

    // Modify 'next' node of bp and root
    PUT(bp_next, original_root_next);
    PUT(lv_root(level), bp);

    // Modify 'prev' node of bp
    PUT(bp, lv_root(level));

    // if bp is not in the tail,
    // modify prev of bp->next node
    if (GET(bp_next) != 0)
        PUT(original_root_next, bp);
}

/* delete node in level list after root */
void delete_node(int level, void *bp) {
    char *bp_prev = bp;
    char *bp_next = NEXT_NODE(bp);

    char *prev = GET(bp_prev);
    char *next = GET(bp_next);

    char *_lv_root = lv_root(level);

    // set prev, next node between two active nodes
    if (prev == _lv_root)
        PUT(_lv_root, next);
    else
        PUT(NEXT_NODE(prev), next);

    if (next != 0)
        PUT(next, prev);

    // set NULL pointer to bp
    PUT(bp, 0);
    PUT(NEXT_NODE(bp), 0);
}

int mm_init(void) {
    /* Create the initial empty heap */
    if ((lv_header = mem_sbrk(4 * WSIZE + 4 * WSIZE)) == (void *)-1)
        return -1;

    /* 4 blocks at the start points the first block of each level.
     * If Lv. header indicates heap_end, it means there is no block in such level.
     * So, in this case, we should walk over another level for finding out
     * the block that is large enough to store the data.
     * 8 bytes (= DWORD) are required for storing pointer
     */

    /* First address is filled with 0 padding for align */
    PUT(lv_header, PACK(0, 0));
    lv_header += 4;

    /* Header for level pointers */
    PUT(lv_header, PACK(2 * WSIZE + 4 * WSIZE, 1));

    /* Footer for level pointers */
    PUT(lv_header + WSIZE + 4 * WSIZE, PACK(2 * WSIZE + 4 * WSIZE, 1));

    /* Epilogue header */
    PUT(lv_header + (2 * WSIZE + 4 * WSIZE), PACK(0, 1));

    lv_header += WSIZE;

    /* End of list will point to NULL*/
    for (int i = 1; i <= 4; i++) {
        PUT(lv_root(i), 0);
    }

    /* Change storage pointer to right after Lv 4 header */
    storage = lv_root(4) + WSIZE + WSIZE;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;
    return 0;
}

/* Check coalescing condition and handle level pointer */
void *coalesce(void *bp) {
    char *root_before;

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    size_t size = GET_SIZE(HDRP(bp));
    size_t level = size_level(size);

    if (prev_alloc && next_alloc) { /* Case 1 */
        /* Correspoinding level to its size */
        insert_node(level, bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc) { /* Case 2 */

        /* Handling prev and next node */
        // Delete two nodes first,
        // and add new node with new size to the new level

        size_t size_next = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        int level_next = size_level(size_next);

        // Delete next node from the level list
        if (NEXT_NODE(bp) != 0)
            delete_node(level_next, NEXT_BLKP(bp));
        // Delete current node from the level list
        if (GET(bp) != 0)
            delete_node(level, bp);

        // coalesced size
        size += size_next;

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) { /* Case 3 */

        /* Handling prev and next node */
        // Delete two nodes first,
        // and add new node with new size to the new level

        size_t size_prev = GET_SIZE(HDRP(PREV_BLKP(bp)));
        int level_prev = size_level(size_prev);

        if (bp != 0)
            delete_node(level_prev, PREV_BLKP(bp));

        /* When the block is extended by extend_heap,
         * there is no prev/next node. So, in this case,
         * delete_node should not be handled to avoid segmentation fault. 
         */
        if (GET(bp) != 0)
            delete_node(level, bp);

        size += size_prev;
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else { /* Case 4 */

        /* Delete three nodes(prev, now, next) */

        size_t size_next = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        int level_next = size_level(size_next);

        size_t size_prev = GET_SIZE(HDRP(PREV_BLKP(bp)));
        int level_prev = size_level(size_prev);

        if (bp != 0)
            delete_node(level_prev, PREV_BLKP(bp));
        if (GET(NEXT_NODE(bp)) != 0)
            delete_node(level_next, NEXT_BLKP(bp));
        if (GET(bp) != 0)
            delete_node(level, bp);

        size += size_prev + size_next;

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // Insert new block in new level
    int new_level = size_level(size);
    insert_node(new_level, bp);

    return bp;
}

void *extend_heap(size_t size) {
    char *bp;

    /* Grow heap with one block that contains data and header/footer. */
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */

    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    PUT(bp, 0);
    PUT(NEXT_NODE(bp), 0);

    heap_end = NEXT_BLKP(bp);

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

void *mm_malloc(size_t size) {
    /* Find appropriate level that can contain data.
     * 1. Search nodes in such level. If any, insert.
     * 2. If there is no node, go to next level and insert.
     * 3. If still cannot find the node, extend the heap and insert.
     */

    // storage == 0 means mem_init has not handled.
    if (storage == 0)
        mem_init();

    size = ALIGN(size);
    int level = size_level(size);

    /* 
     * Search empty block on the list with determined level using First-fit method.
     * If any, return. 
     * If not, go to higher level and search again.
     * Do this job recursively with while loop.
     * 
     * 
     * The size of block is restricted to minimum 24 bytes
     * since it has to store two pointers + header, footer when empty.
     * size + 8 = data + footer + header.
     */
    size_t asize = MAX(MIN_SIZE, size + 8);

    for (int i = level; i <= 4; i++) {
        // 'tmp' is used for level-list walk
        char *tmp = GET(lv_root(i));
        while (tmp != 0) {
            if (GET_ALLOC(HDRP(tmp)) == 0 && (GET_SIZE(HDRP(tmp)) >= asize)) {
                /* Found the empty block with enough size. Insert here! */
                place(tmp, asize);
                return tmp;
            }
            tmp = GET(NEXT_NODE(tmp));
        }
    }

    /*
     * Could not find the right position to place the data.
     * Now, extend the heap and place.
     * mem_heap_hi indicates the address of heap_end block.
     */
    if (GET_ALLOC(heap_end - 2 * WSIZE) == 0)
        asize -= GET_SIZE(heap_end - 2 * WSIZE);
    char *pos = extend_heap(asize);
    place(pos, size + 8);

    return pos;
}

/* place() function not only places the data in the block,
 * but also handle the split of empty block. 
 * For example, when the block with size of 32 is filled by
 * malloc(8), 24 bytes remain and its level list should be changed.
 */

void place(void *bp, int alloc_size) {
    size_t before_size = GET_SIZE(HDRP(bp));
    size_t free_remain = before_size - alloc_size;

    /* 
     * if the remaining free block size is smaller than MIN 24 bytes,
     * split can't be held. Just change the alloc bit.
     */

    if (free_remain < MIN_SIZE) {
        PUT(FTRP(bp), PACK(before_size, 1));
        PUT(HDRP(bp), PACK(before_size, 1));
        delete_node(size_level(before_size), bp);
        return;
    }

    /*
     * If remaining free bytes is larger than MIN 16 bytes, split the block.
     * Change the information of block in the header and footer.
     * alloc bit = 1, size = alloc_size
     */

    PUT(HDRP(bp), PACK(alloc_size, 1));
    PUT(FTRP(bp), PACK(alloc_size, 1));
    delete_node(size_level(before_size), bp);

    /* 
     * Information of remaining block is as follows.
     * alloc = 0, size = free_remain
     */
    char *remain = NEXT_BLKP(bp);
    PUT(HDRP(remain), PACK(free_remain, 0));
    PUT(FTRP(remain), PACK(free_remain, 0));

    /*
     * Now, insert the remain block to appropriate level list
     */
    coalesce(remain);
}

void mm_free(void *ptr) {
    /*
     * 1. Change the information of block. alloc 1 -> 0
     * 2. Set the data, which was prev/next pointer, to 0. 
     * 3. Coalesce.
     */
    if (ptr == NULL)
        return;

    if (storage == 0)
        mem_init();

    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(ptr, 0);
    PUT(NEXT_NODE(ptr), 0);

    coalesce(ptr);
}

void *mm_realloc(void *ptr, size_t size) {

    if (ptr == NULL)
        return mm_malloc(size);

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    size_t oldsize = GET_SIZE(HDRP(ptr));

    /* Define the block size and align */
    size_t asize = MAX(MIN_SIZE, ALIGN(size + 8));

    /* Case 1. Recalled block size shrinks */
    if (asize < oldsize) {
        /* 
         * Modify the size of ptr in the header and footer.
         * Block is splitted into two sections.
         * Realloced(alloc = 1) + Free (alloc = 0)
         * Free block would have the size of (old_size - asize). 
         */
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        char *free_block = NEXT_BLKP(ptr);
        PUT(HDRP(free_block), PACK(oldsize - asize, 0));
        PUT(FTRP(free_block), PACK(oldsize - asize, 0));

        mm_free(free_block);

        return ptr;

        /* Case 2. Recalled block size is identical to the old one. */
    } else if (asize == oldsize) {
        /*
         * In this case, we don't have to modify the block.
         */
        return ptr;

        /* Case 3. Recalled block size is BIGGER than old one */
    } else {
        /*
         * Check the size of the block behind. NEXT_BLKP(ptr)
         * Calculate the size that would be added(req_size).
         * 
         *  If the next block size is larger than req_size + 10,
         *  realloc the block as usual and modify remainder as another free block. 
         *  Block size 10 is arbitrarily determined.
         * 
         *  ******** req_size does not take header and footer into account.
         * 
         */

        char *next_block = NEXT_BLKP(ptr);
        size_t next_size = GET_SIZE(HDRP(next_block));
        size_t req_size = asize - oldsize;

        if (next_size >= req_size + 10) {
            /* Reallocation. Change the size of block in the header and footer. */
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));

            /* Handle the remainder block. */
            char *free_block = NEXT_BLKP(ptr);
            PUT(HDRP(free_block), PACK(req_size, 0));
            PUT(FTRP(free_block), PACK(req_size, 0));
            mm_free(free_block);
        }

        /*
         * The size of remainder block is small but still can contain req_size.
         * So, just take the block as dummy.
         */ 
        else if (next_size < req_size + 10 && next_size > req_size) {
            PUT(HDRP(ptr), PACK(oldsize + next_size, 1));
            PUT(FTRP(ptr), PACK(oldsize + next_size, 1));
            /* Fill the uninitialized region with 0 padding */
            for (char *tmp = ptr; tmp < HDRP(ptr); tmp++) {
                PUT(tmp, 0);
            }
        }

        /*
         * Next block is still not enough to realloc.
         * Use malloc to make block(with asize), and move the data to appropriate place.
         * Original block is freed.
         */

        else {
            char *mv = mm_malloc(asize);
            memcpy(mv, ptr, oldsize - 2*WSIZE); // memcpy only the data.
            mm_free(ptr);
        }
    }
}
