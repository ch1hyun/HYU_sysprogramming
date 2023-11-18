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
#define NEXT_FITx

/* Team structure (this should be one-man team, meaning that you are the only member of the team) */
team_t team = {
#ifdef NEXT_FIT
    "segregate next fit", 
#else
    "segregate first fit", 
#endif
    "오치현", "2021029889", /* your name and student id in quote */
    "", ""
}; 

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define DDSIZE      16       /* doubledoubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */
#define RANK0       (WSIZE<<3)      /* Rank 0 의 범위는 4 ~ 8 워드 입니다. */
#define RANK1       (WSIZE<<4)      /* Rank 1 의 범위는 10 ~ 16 워드 입니다. */
#define RANK2       (RANK0 | RANK1)      /* Rank 2 의 범위는 18 ~ 24 워드 입니다. */
#define RANK3       (WSIZE<<5)      /* Rank 3 의 범위는 18 ~ 32 워드 입니다. */
#define RANK4       (WSIZE<<6)      /* Rank 4 의 범위는 34 ~ 64 워드 입니다. */
#define RANK5       (WSIZE<<7)      /* Rank 5 의 범위는 66 ~ 128 워드 입니다. */
#define RANK6       (WSIZE<<8)      /* Rank 6 의 범위는 130 ~ 256 워드 입니다. */
#define RANK7       (WSIZE<<9)      /* Rank 7 의 범위는 258 ~ 512 워드 입니다. */
#define RANK8       (WSIZE<<10)      /* Rank 8 의 범위는 514 ~ 1024 워드 입니다. */
                                    /* Rank 9 의 범위는 1026 ~ INF 워드 입니다. */
#define RANKSIZE    10

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

/* 프리리스트에 연결된 노드의 다음 또는 이전 프리 블록 포인터 반환 */
#define GET_NEXT(bp)    (*(void**)((char *)(bp) + WSIZE))
#define GET_PREV(bp)    (*(void**)(bp))

/* 프리리스트 계층에 해당하는 헤더 포인터 반환 */
#define GET_RANK(rank)  (*(void**)((char *)(heap_listp) + (WSIZE*rank)))

/* 2 워드 사이즈 단위로 올림 */
#define ALIGN(size)     (DSIZE * ((size + DDSIZE - 1) / DSIZE))
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

void escape(void *bp);
void insert(void *bp);
size_t getRank(size_t size);

/* 
 * mm_init - Initialize the memory manager 
 */
/* $begin mminit */
int mm_init(void) 
{
    /* create the initial empty heap */
    if ((heap_listp = mem_sbrk((RANKSIZE+4)*WSIZE)) == (void *)-1)
	return -1;
    PUT(heap_listp, 0);                        /* alignment padding */
    PUT(heap_listp+(1*WSIZE), PACK((RANKSIZE+2)*WSIZE, 1));  /* prologue header */ 
    for (int i = 2; i - 2 < RANKSIZE; ++i) {
        PUT(heap_listp+(i*WSIZE), NULL); /* 프리 리스트 포인터 */
    }
    PUT(heap_listp+((RANKSIZE+2)*WSIZE), PACK((RANKSIZE+2)*WSIZE, 1));  /* prologue footer */ 
    PUT(heap_listp+((RANKSIZE+3)*WSIZE), PACK(0, 1));  /* epilogue header */ 
    heap_listp += DSIZE;

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
    void *bp;

    if (size <= DSIZE) { // 최소 할당 사이즈는 4 워드
        asize = DDSIZE;
    } else {
        asize = ALIGN(size);
    }

    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize); // 필요 공간만 할당
        if (!GET_ALLOC(HDRP(bp))) { // 분할될 때 사이즈가 24 워드보다 크다면, 나누어진 공간의 뒤의 공간이 할당됨
            bp = NEXT_BLKP(bp);
        }
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE); // 청크 사이즈와 요구 사이즈 중 큰 것

    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;

    place(bp, asize);
    if (!GET_ALLOC(HDRP(bp))) {
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
        size = DDSIZE;
    } else {
        size = ALIGN(size);
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
        /* 요구 사이즈가 현재 사이즈 보다 작고, 현재 할당 공간에서 분할할 때 남은 공간이 4 워드보다 큰 경우 */
        if (size < csize && cur_new >= DDSIZE) {
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(FTRP(ptr), PACK(size, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(cur_new, 0));
            PUT(FTRP(NEXT_BLKP(ptr)), GET(HDRP(NEXT_BLKP(ptr))));
            insert(NEXT_BLKP(ptr));
            return ptr;
        }
    }

    /* CASE 2 */
    /* | ALLOC | ALLOC | FREE | */
    else if (prev_alloc && !next_alloc) {
        /* 요구 사이즈가 현재 사이즈 보다 작은 경우, 현재 할당 공간에서 분할한 뒤, 다음 프리 블록과 병합 */
        if (size < csize) {
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(FTRP(ptr), PACK(size, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(cur_new, 0));
            PUT(FTRP(NEXT_BLKP(ptr)), GET(HDRP(NEXT_BLKP(ptr))));
            coalesce(NEXT_BLKP(ptr));
            return ptr;
        }
        /* 요구 사이즈를 충족하기 위한 추가 사이즈 만큼의 공간을 다음 프리 블록에서 가져왔을 때 남은 프리 블록 공간이 4 워드 이상인 경우 */
        else if ((next_size - new_cur) >= DDSIZE) {
            escape(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(FTRP(ptr), PACK(size, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(next_size - new_cur, 0));
            PUT(FTRP(NEXT_BLKP(ptr)), GET(HDRP(NEXT_BLKP(ptr))));
            insert(NEXT_BLKP(ptr));
            return ptr;
        }
    }

    /* CASE 3 */
    /* | FREE | ALLOC | ALLOC | */
    else if (!prev_alloc && next_alloc) {
        /* 요구 사이즈가 현재 사이즈 보다 작은 경우, 현재 할당 공간에서 분할한 뒤, 이전 프리 블록과 병합 */
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
        /* 요구 사이즈를 충족하기 위한 추가 사이즈 만큼의 공간을 이전 프리 블록에서 가져왔을 때 남은 프리 블록 공간이 4 워드 이상인 경우 */
        else if ((prev_size - new_cur) >= DDSIZE) {
            escape(PREV_BLKP(ptr));
            PUT(HDRP(PREV_BLKP(ptr)), PACK(prev_size - new_cur, 0));
            PUT(FTRP(PREV_BLKP(ptr)), GET(HDRP(PREV_BLKP(ptr))));
            void *new_ptr = NEXT_BLKP(PREV_BLKP(ptr));
            memmove(new_ptr, ptr, csize-DSIZE);
            PUT(HDRP(new_ptr), PACK(size, 1));
            PUT(FTRP(new_ptr), PACK(size, 1));
            insert(PREV_BLKP(new_ptr));
            return new_ptr;
        }
    }

    /* CASE 4 abc*/
    /* | FREE | ALLOC | FREE | */
    else if (!prev_alloc && !next_alloc) {
        /* 사이즈 변경 후 남은 양쪽 프리 블록을 포함해 크기가 4 워드 이상일 경우 */
        if ((prev_size + next_size - new_cur) >= DDSIZE) {
            size_t pnmn = prev_size + next_size - new_cur;
            escape(PREV_BLKP(ptr));
            escape(NEXT_BLKP(ptr));
            /* 할당 공간이 25 워드를 넘어가는 경우, 뒤에 배치 */
            if (size >= 100) {
                PUT(HDRP(PREV_BLKP(ptr)), PACK(pnmn, 0));
                void *new_ptr = NEXT_BLKP(PREV_BLKP(ptr));
                memmove(new_ptr, ptr, size-DSIZE);
                PUT(new_ptr-DSIZE, PACK(pnmn, 0));
                PUT(HDRP(new_ptr), PACK(size, 1));
                PUT(FTRP(new_ptr), PACK(size, 1));
                insert(PREV_BLKP(new_ptr));
                return new_ptr;
            } else { /* 넘어가지 않는 경우, 앞에 배치 */
                void *new_ptr = PREV_BLKP(ptr);
                PUT(HDRP(new_ptr), PACK(size, 1));
                memmove(new_ptr, ptr, size-DSIZE);
                PUT(FTRP(new_ptr), PACK(size, 1));
                PUT(HDRP(NEXT_BLKP(new_ptr)), PACK(pnmn, 0));
                PUT(FTRP(NEXT_BLKP(new_ptr)), PACK(pnmn, 0));
                insert(NEXT_BLKP(new_ptr));
                return new_ptr;
            }
        }
    }

    /* 위의 조건을 모두 만족하지 않는 경우, 최적의 공간 배치의 경우가 없는 것으로 간주하고 현재 블록을 해제 후 재할당 */
    void *new_ptr;
    if ((new_ptr = mm_malloc(size)) == NULL) {
        return NULL;
    }

    /* memcpy를 사용해서 메모리에서 바로 복사 후 붙여넣기를 하는 것보다 memmove를 사용해서 기존 메모리 값을 버퍼에 복사 후 새로운 곳에 붙여넣기를 하는 것이 더 안정적임. */
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

    if ((GET_SIZE(HDRP(heap_listp)) != (RANKSIZE+2)*WSIZE) || !GET_ALLOC(HDRP(heap_listp)))
	printf("Bad prologue header\n");
    checkblock(heap_listp);

    /* 모든 프리 블록이 리스트에 있는지 테스트 */
    toggleMarkFreeBlock();
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && !(GET(HDRP(bp))&4)) {
            printf("프리 리스트에 없는 프리 블록이 존재합니다.\n");
            printblock(bp);
        }
	if (verbose) 
	    printblock(bp);
	checkblock(bp);
    }
    toggleMarkFreeBlock();
     
    if (verbose)
	printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
	printf("Bad epilogue header\n");
}

void toggleMarkFreeBlock() {
    size_t rank = 0;
    void *bp;
    while (rank < RANKSIZE) {
        for (bp = GET_RANK(rank); bp != NULL; bp = GET_NEXT(bp)) {
            PUT(HDRP(bp), GET(HDRP(bp)) ^ 4);
        }
        ++rank;
    }
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
    /* 프리 리스트에서 제거 */
    escape(bp);
    size_t csize = GET_SIZE(HDRP(bp));   
    size_t remainder = csize - asize;

    if (remainder <= DDSIZE) {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    /* 사이즈가 24 워드보다 큰 경우 뒤에 배치 */
    else if (asize >= ((WSIZE<<4)|(WSIZE<<2))) {
        PUT(HDRP(bp), PACK(remainder, 0));
        PUT(FTRP(bp), PACK(remainder, 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
        /* 남은 공간 프리리스트에 삽입 */
        insert(bp);
    }
    /* 앞에 배치 */
    else {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remainder, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remainder, 0));
        insert(NEXT_BLKP(bp));
    }
}
/* $end mmplace */

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
#ifdef NEXT_FIT 
    /* next fit search */
    char *oldrover = rover;

    /* search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
	    return rover;

    /* search from start of list to old rover */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
	if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
	    return rover;

    return NULL;  /* no fit found */
#else 
    /* first fit search */
    size_t rank = getRank(asize);
    void *bp;

    /* 크기를 기준으로 삽입되었을 프리리스트 헤더 포인터 받은 후, 계층을 올려가며 탐색 */
    while (rank < RANKSIZE) {
        for (bp = GET_RANK(rank); bp != NULL; bp = GET_NEXT(bp)) {
            if (asize <= GET_SIZE(HDRP(bp))) {
                return bp;
            }
        }

        ++rank; // 계층 올리기
    }

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
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2 */
    escape(NEXT_BLKP(bp));
	size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3 */
    escape(PREV_BLKP(bp));
	size += GET_SIZE(HDRP(PREV_BLKP(bp)));
	PUT(FTRP(bp), PACK(size, 0));
	PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	bp = PREV_BLKP(bp);
    }

    else {                                     /* Case 4 */
    escape(NEXT_BLKP(bp));
    escape(PREV_BLKP(bp));
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
    insert(bp);

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

/* Private Functions */
/* 사이즈에 맞는 계층 번호를 반환하는 함수 */
size_t getRank(size_t size) {
    if (size <= RANK0) return 0;
    if (size <= RANK1) return 1;
    if (size <= RANK2) return 2;
    if (size <= RANK3) return 3;
    if (size <= RANK4) return 4;
    if (size <= RANK5) return 5;
    if (size <= RANK6) return 6;
    if (size <= RANK7) return 7;
    if (size <= RANK8) return 8;
    return 9;
}

/* FIFO */
/* 프리리스트에 프리 블록을 삽입 시키는 함수 */
void insert(void *bp) {
    size_t rank = getRank(GET_SIZE(HDRP(bp)));

    GET_NEXT(bp) = GET_RANK(rank);
    /* NULL이 아니면, 첫 번째 프리 블록의 이전 노드로 현재 노드를 지정해줘야 함 */
    if (GET_RANK(rank) != NULL) {
        GET_PREV(GET_RANK(rank)) = bp;
    }
    GET_RANK(rank) = bp;
}

/* 프리리스트에서 프리 블록을 제외 시키는 함수 */
void escape(void *bp) {
    size_t rank = getRank(GET_SIZE(HDRP(bp)));

    /* 프리 리스트 헤더가 가리키는 첫 번째 노드가 현재 노드인 경우 */
    if (bp == GET_RANK(rank)) {
        GET_RANK(rank) = GET_NEXT(GET_RANK(rank));
        return;
    }

    /* 이전 노드와 다음 노드를 연결해줌 */
    GET_NEXT(GET_PREV(bp)) = GET_NEXT(bp);
    if (GET_NEXT(bp) != NULL) {
        GET_PREV(GET_NEXT(bp)) = GET_PREV(bp);
    }
}