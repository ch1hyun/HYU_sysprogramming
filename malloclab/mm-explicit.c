/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include "mm.h"
#include "memlib.h"

/*
 * If NEXT_FIT defined use next fit search, else use first fit search 
 */
#define NEXT_FIT 1

/* Team structure (this should be one-man team, meaning that you are the only member of the team) */
team_t team = {
#ifdef NEXT_FIT
    "explicit next fit", 
#else
    "implicit first fit", 
#endif
    "오치현", "2021029889", /* your name and student id in quote */
    "", ""
}; 

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  
#define MIN(x, y) ((x) < (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NEXT(bp) (*(void **)((char *)(bp) + WSIZE))
#define PREV(bp) (*(void **)(bp))
/* $end mallocmacros */

/* Global variables */
static char *heap_listp;  /* pointer to first block */  
#ifdef NEXT_FIT
static char *rover;       /* next fit rover */
#endif

/* function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
    void *temp_heap_listp;
    /* create the initial empty heap */
    if ((temp_heap_listp = mem_sbrk((DSIZE<<2))) == (void *)-1)
	return -1;
    PUT(temp_heap_listp, 0);                        /* alignment padding */
    PUT(temp_heap_listp+(WSIZE), PACK(DSIZE, 1));  /* prologue header */ 
    PUT(temp_heap_listp+(DSIZE), PACK(DSIZE, 1));  /* prologue footer */ 
    PUT(temp_heap_listp+(DSIZE+WSIZE), PACK((DSIZE<<1), 0));  /* dummy header */ 
    PUT(temp_heap_listp+(DSIZE<<1), temp_heap_listp+((DSIZE<<1)));  /* prev pointer */ 
    PUT(temp_heap_listp+((DSIZE<<1)+WSIZE), temp_heap_listp+((DSIZE<<1)));  /* next pointer */ 
    PUT(temp_heap_listp+((DSIZE<<1)+DSIZE), PACK((DSIZE<<1), 0));  /* dummy footer */ 
    PUT(temp_heap_listp+((DSIZE<<1)+DSIZE+WSIZE), PACK(0, 1));  /* epilogue header */ 
    heap_listp = temp_heap_listp + (DSIZE<<1);

#ifdef NEXT_FIT
    rover = heap_listp;
#endif

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
	return -1;
    return 0;
}
/* $end mminit */

/* 
 * mm_malloc - Allocate a block with at least size bytes of payload 
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) 
{
    size_t asize;
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;
    
    if (size <= DSIZE) {
        asize = (DSIZE<<1);
    } else {
        asize = DSIZE * ((size + (DSIZE<<1) - 1) / DSIZE);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        if (GET_ALLOC(HDRP(bp)) != 1) {
            bp = NEXT_BLKP(bp);
        }
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }

    place(bp, asize);
    if (GET_ALLOC(HDRP(bp)) != 1) {
        bp = NEXT_BLKP(bp);
    }
    return bp;
} 
/* $end mmmalloc */

/* 
 * mm_free - Free a block 
 */
/* $begin mmfree */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    // 포인터가 널이면, malloc 과 같은 동작을 한다.
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    // 사이즈가 0이면 free 와 같은 동작을 한다.
    if (size == 0) {
        mm_free(ptr);
    }

    size_t csize = GET_SIZE(HDRP(ptr));

    if (size <= DSIZE) {
        size = 2*DSIZE;
    } else {
        size = DSIZE * ((size + 2*DSIZE - 1) / DSIZE);
    }

    // 사이즈가 같으면 다시 반환한다.
    if (size == csize) {
        return ptr;
    }

    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
    size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(ptr)));
    size_t new_cur = size - csize;
    size_t cur_new = csize - size;

    /* CASE 1 */
    /* | ALLOC | ALLOC | ALLOC | */
    if (prev_alloc && next_alloc) {
        if (size < csize && cur_new >= 4*WSIZE) {
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(FTRP(ptr), PACK(size, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(cur_new, 0));
            PUT(FTRP(NEXT_BLKP(ptr)), GET(HDRP(NEXT_BLKP(ptr))));
            insert_list(NEXT_BLKP(ptr));
            return ptr;
        }
    }

    /* CASE 2 */
    /* | ALLOC | ALLOC | FREE | */
    else if (prev_alloc && !next_alloc) {
        if (size < csize) {
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(FTRP(ptr), PACK(size, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(cur_new, 0));
            PUT(FTRP(NEXT_BLKP(ptr)), GET(HDRP(NEXT_BLKP(ptr))));
            coalesce(NEXT_BLKP(ptr));
            return ptr;
        }
        else if ((next_size - new_cur) >= 4*WSIZE) {
            escape_list(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(FTRP(ptr), PACK(size, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(next_size - new_cur, 0));
            PUT(FTRP(NEXT_BLKP(ptr)), GET(HDRP(NEXT_BLKP(ptr))));
            insert_list(NEXT_BLKP(ptr));
            return ptr;
        }
    }

    /* CASE 3 */
    /* | FREE | ALLOC | ALLOC | */
    else if (!prev_alloc && next_alloc) {
        if (size < csize) {
            PUT(HDRP(ptr), PACK(cur_new, 0));
            memmove(NEXT_BLKP(ptr), ptr, size-DSIZE);
            PUT(FTRP(ptr), GET(HDRP(ptr)));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(size, 1));
            PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 1));
            ptr = NEXT_BLKP(ptr);
            coalesce(PREV_BLKP(ptr));
            return ptr;
        }
        else if ((prev_size - new_cur) >= 4*WSIZE) {
            escape_list(PREV_BLKP(ptr));
            PUT(HDRP(PREV_BLKP(ptr)), PACK(prev_size - new_cur, 0));
            PUT(FTRP(PREV_BLKP(ptr)), GET(HDRP(PREV_BLKP(ptr))));
            void *new_ptr = NEXT_BLKP(PREV_BLKP(ptr));
            memmove(new_ptr, ptr, csize-DSIZE);
            PUT(HDRP(new_ptr), PACK(size, 1));
            PUT(FTRP(new_ptr), PACK(size, 1));
            insert_list(PREV_BLKP(new_ptr));
            return new_ptr;
        }
    }

    /* CASE 4 abc*/
    /* | FREE | ALLOC | FREE | */
    else if (!prev_alloc && !next_alloc) {
        if ((prev_size + next_size - new_cur) >= 4*WSIZE) {
            size_t pnmn = prev_size + next_size - new_cur;
            escape_list(PREV_BLKP(ptr));
            escape_list(NEXT_BLKP(ptr));
            if (size >= 100) {
                PUT(HDRP(PREV_BLKP(ptr)), PACK(pnmn, 0));
                void *new_ptr = NEXT_BLKP(PREV_BLKP(ptr));
                memmove(new_ptr, ptr, size-DSIZE);
                PUT(new_ptr-DSIZE, PACK(pnmn, 0));
                PUT(HDRP(new_ptr), PACK(size, 1));
                PUT(FTRP(new_ptr), PACK(size, 1));
                insert_list(PREV_BLKP(new_ptr));
                return new_ptr;
            } else {
                void *new_ptr = PREV_BLKP(ptr);
                PUT(HDRP(new_ptr), PACK(size, 1));
                memmove(new_ptr, ptr, size-DSIZE);
                PUT(FTRP(new_ptr), PACK(size, 1));
                PUT(HDRP(NEXT_BLKP(new_ptr)), PACK(pnmn, 0));
                PUT(FTRP(NEXT_BLKP(new_ptr)), PACK(pnmn, 0));
                insert_list(NEXT_BLKP(new_ptr));
                return new_ptr;
            }
        }
    }

    void *new_ptr;
    if ((new_ptr = mm_malloc(size)) == NULL) {
        return NULL;
    }

    memmove(new_ptr, ptr, MIN(size, csize)-DSIZE);

    mm_free(ptr);

    return new_ptr;
}

/* 
 * mm_checkheap - Check the heap for consistency 
 */
void mm_checkheap(int verbose) 
{
    char *bp = heap_listp;

    if (verbose)
	printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
	if (verbose) 
	    printblock(bp);
	checkblock(bp);
    }
     
    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/* 
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;
	
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((bp = mem_sbrk(size)) == (void *)-1) 
	return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}
/* $end mmextendheap */

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    escape_list(bp);
    size_t csize = GET_SIZE(HDRP(bp));   
    size_t remainer = csize - asize;

    if (remainer <= (DSIZE<<1)) {
	    PUT(HDRP(bp), PACK(csize, 1));
    	PUT(FTRP(bp), PACK(csize, 1));
    }

    else if (asize >= 100) {
        PUT(HDRP(bp), PACK(remainer, 0));
        PUT(FTRP(bp), PACK(remainer, 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
        insert_list(bp);
    }
    else {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remainer, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remainer, 0));
        insert_list(NEXT_BLKP(bp));
    }
}
/* $end mmplace */

void escape_list(void *bp) {
    void **temp_heap_listp = &heap_listp;
    if (bp == *temp_heap_listp) {
        if (bp == NEXT(bp)) {
            rover = *temp_heap_listp = NULL;
            return;
        }

        *temp_heap_listp = NEXT(bp);
    }

    if (rover == bp) {
        rover = NEXT(bp);
    }

    NEXT(PREV(bp)) = NEXT(bp);
    PREV(NEXT(bp)) = PREV(bp);
}

void insert_list(void *bp) {
    void **temp_heap_listp = &heap_listp;
    if (*temp_heap_listp == NULL) {
        NEXT(bp) = bp;
        PREV(bp) = bp;
        rover = *temp_heap_listp = bp;
        return;
    }

    NEXT(bp) = *temp_heap_listp;
    PREV(bp) = PREV(*temp_heap_listp);
    PREV(NEXT(bp)) = bp;
    NEXT(PREV(bp)) = bp;
    *temp_heap_listp = bp;
}

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
#ifdef NEXT_FIT 
    if (rover == NULL) return NULL;

    /* next fit search */
    char *oldrover, *currover;
    oldrover = currover = PREV(rover);

    do {
        currover = NEXT(currover);

        if (asize <= GET_SIZE(HDRP(currover))) {
            return (rover = currover);
        }
    } while(oldrover != currover);

    rover = currover;
    return NULL;  /* no fit found */
#else 
    /* first fit search */
    if (heap_listp == NULL) return NULL;

    void *bp, *last;
    bp = last = PREV(heap_listp);

    do {
        bp = NEXT(bp);

        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
    } while (bp != last);

    return NULL; /* no fit */
#endif
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {            /* Case 1 */
        insert_list(bp);
    	return bp;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
    escape_list(NEXT_BLKP(bp));
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
    escape_list(PREV_BLKP(bp));
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
    escape_list(NEXT_BLKP(bp));
    escape_list(PREV_BLKP(bp));
	size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
	    GET_SIZE(FTRP(NEXT_BLKP(bp)));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
    }

#ifdef NEXT_FIT
    /* Make sure the rover isn't pointing into the free block */
    /* that we just coalesced */
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp))) 
	rover = bp;
#endif

    insert_list(bp);
    return bp;
}


static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  
    
    if (hsize == 0) {
	printf("%p: EOL\n", bp);
	return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp, 
	   hsize, (halloc ? 'a' : 'f'), 
	   fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    if ((size_t)bp % 8)
	printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
	printf("Error: header does not match footer\n");
}



