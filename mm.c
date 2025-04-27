/*
 * mm-implicit.c - implicit free-list malloc package (next-fit)
 *
 * This implementation uses an implicit free list with
 * next-fit placement, boundary tag coalescing,
 * and prologue/epilogue blocks.
 * Blocks are aligned to 8 bytes, and minimum block size is 16 bytes.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * Team information
 *********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE   (1<<12) /* Extend heap by this amount (bytes) */
#define MAX(x, y)   ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global pointers */
static char *heap_listp;  /* Points to first block */
static char *rover = NULL;       /* Next-fit rover pointer */

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);                            /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += 2 * WSIZE;

    /* Initialize rover for next-fit */
    rover = heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * extend_heap - extend heap with free block and return its block pointer
 */

// 누나 코드

// static void *extend_heap(size_t words)
// {
//     char *bp;
//     size_t size;

//     /* Allocate an even number of words to maintain alignment */
//     size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
//     if ((long)(bp = mem_sbrk(size)) == -1)
//         return NULL;

//     /* Initialize free block header/footer and the epilogue header */
//     PUT(HDRP(bp), PACK(size, 0));          /* Free block header */
//     PUT(FTRP(bp), PACK(size, 0));          /* Free block footer */
//     PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  /* New epilogue header */

//     /* Coalesce if the previous block was free */
//     return coalesce(bp);
// }

// /*
//  * coalesce - boundary tag coalescing. Return ptr to coalesced block
//  */
// static void *coalesce(void *bp)
// {
//     size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
//     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
//     size_t size = GET_SIZE(HDRP(bp));

//     if (prev_alloc && next_alloc) {            /* Case 1 */
//         return bp;
//     } else if (prev_alloc && !next_alloc) {    /* Case 2 */
//         size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
//         PUT(HDRP(bp), PACK(size, 0));
//         PUT(FTRP(bp), PACK(size, 0));
//         return bp;
//     } else if (!prev_alloc && next_alloc) {    /* Case 3 */
//         size += GET_SIZE(HDRP(PREV_BLKP(bp)));
//         bp = PREV_BLKP(bp);
//         PUT(HDRP(bp), PACK(size, 0));           // 새 헤더 기록
//         PUT(FTRP(bp), PACK(size, 0)); 
//         return bp;
//     } else {                                   /* Case 4 */
//         size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
//                 GET_SIZE(FTRP(NEXT_BLKP(bp)));
//         bp = PREV_BLKP(bp);
//         PUT(HDRP(bp), PACK(size, 0));
//         PUT(FTRP(bp), PACK(size, 0));
//         // PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
//         // PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
//         // bp = PREV_BLKP(bp);
//         return bp;
//     }
    
// }

/* 힙을 words * WSIZE 바이트 만큼 확장하고 새로운 가용 블록 생성 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 짝수 워드로 맞추어 8바이트 정렬 유지 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* 새로 생성된 블록의 헤더와 푸터 설정 (가용 상태) */
    PUT(HDRP(bp), PACK(size, 0));              /* 가용 블록 헤더 */
    PUT(FTRP(bp), PACK(size, 0));              /* 가용 블록 푸터 */
    /* 새로운 에필로그 블록 헤더 설정 (크기=0, 할당됨) */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp); /* 인접 블록과 병합하여 커다란 블록 반환 */
}

// coalesce: 인접 블록이 free면 합쳐주기
static void *coalesce(void *bp)
{
    // 이전 블록 free, 할당 여부
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); 
    // 다음 블록 free, 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 현재 블록 크기
    size_t size = GET_SIZE(HDRP(bp));             

    // Case1: 이전과 다음 모두 할당된 경우
    if (prev_alloc && next_alloc) {
        return bp;
    }
    // Case2: 이전 할당, 다음 free인 경우
    else if (prev_alloc && !next_alloc) {
        // 다음 블록 크기 추가
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));         

        // 병합된 내용을 헤더와, 풋터에 추가
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    // Case3: 이전 free, 다음 할당
    else if (!prev_alloc && next_alloc) {
        // 이전 블록 크기 추가
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));         

        // 이전 블록의 헤더와 현재 푸터에 병합된 내용 추가
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        // 병합 후 새 블록 포인터로 수정
        bp = PREV_BLKP(bp);
    }
    // Case4: 이전과 다음 모두 free
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        /* 이전 헤더와 다음 푸터를 병합된 크기로 설정 */
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}

/*
 * find_fit - find a fit for a block with asize bytes (next-fit search)
 */
static void *find_fit(size_t asize)
{
    char *bp;

    /* Search from rover to end of heap */
    for (bp = rover; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)) {
            rover = bp; /* update rover */
            return bp;
        }
    }
    /* Search from start of heap to rover */
    for (bp = heap_listp; bp < rover; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)) {
            rover = bp; /* update rover */
            return bp;
        }
    }
    return NULL; /* no fit found */
}

/*
 * place - place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        char *next_bp = NEXT_BLKP(bp);
        PUT(HDRP(next_bp), PACK(csize - asize, 0));
        PUT(FTRP(next_bp), PACK(csize - asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Free a block
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newptr;
    size_t copySize;

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    /* Copy the old data */
    copySize = GET_SIZE(HDRP(ptr)) - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, ptr, copySize);
    mm_free(ptr);
    return newptr;
}