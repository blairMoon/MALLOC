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
#define ALIGNMENT 8  // 8바이트 정렬

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7) // 8의 배수로 맞추기

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE       4        // Word 크기 (4바이트)
#define DSIZE       8       // Double Word 크기 (8바이트)
#define CHUNKSIZE   (1<<12) // 4096바이트 (힙 확장 크기)

#define MAX(x, y)   ((x) > (y) ? (x) : (y)) // 둘 중 큰 값


/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))
// size + alloc을 한 번에 저장.
// 할당 비트(alloc)는 마지막 1비트 (0x1)로 저장함.



/* Read and write a word at address p */
#define GET(p)      (*(unsigned int *)(p)) //p 위치에서 4바이트짜리 값을 가져옴.
#define PUT(p, val) (*(unsigned int *)(p) = (val)) //p 위치에 4바이트짜리 값을 넣음.

/* Read the size and allocated fields from address p */ 
//헤더 푸터 다루는 용 
#define GET_SIZE(p)     (GET(p) & ~0x7) //블록 크기만 꺼냄.(마지막 3비트는 0으로)
#define GET_ALLOC(p)    (GET(p) & 0x1) //할당 여부만 꺼냄. (맨 마지막 비트)

/* Given block ptr bp, compute address of its header and footer */

// #define HDRP(bp)  ((char *)(bp) - WSIZE)
// #define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - WSIZE)

// #define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))    
// #define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - WSIZE)))



#define HDRP(bp)    ((char *)(bp) - WSIZE)
// HDRP(bp): 헤더 위치로 이동.
// bp는 payload 시작 주소니까, 4바이트 앞으로 가면 헤더임.
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
// 푸터(footer)는 1 word = 4 바이트(WSIZE) 입니다.
// #define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - WSIZE)
// 그런데 위 매크로는 **8 바이트(DSIZE)**를 빼고 있어서
// 푸터 위치가 4바이트 “앞”으로 당겨짐 → 다음 블록 헤더가 payload를 침범
// 결과적으로 mdriver가 **“payload가 서로 겹친다”**고 보고합니다.


// FTRP(bp): 푸터 위치로 이동.
// 헤더의 크기만큼 이동한 다음, 푸터 크기만큼(8바이트) 빼줘.
/* Given block ptr bp, compute address of next and previous blocks */
//NEXT_BLKP(bp): 다음 블록으로 이동.
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
// PREV_BLKP(bp): 이전 블록으로 이동.
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define OVERHEAD (2 * WSIZE)   // 헤더(4) + 푸터(4) = 8바이트



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
// 힙 만들고 프롤로그 / 에필로그 블록 세팅
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)  // 힙 공간 16바이트 할당
        return -1;
    PUT(heap_listp, 0);                            // 패딩 (8바이트 정렬용)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 헤더 (8바이트, 할당됨)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 프롤로그 푸터 (8바이트, 할당됨)
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 에필로그 헤더 (크기 0, 할당됨)
    heap_listp += 2 * WSIZE;                       // payload 시작 위치로 이동

    rover = heap_listp;  // next-fit 탐색 시작 위치 설정

    // 초기 힙 확장 (4096바이트)
    // if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
    //     return -1;                       /* 한번만 확장 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    if (extend_heap(4) == NULL)
        return -1;
    return 0;
}
void *mm_malloc(size_t size)  // size: 사용자가 요청한 메모리 크기 (payload 크기)
{
    size_t asize;        // 조정된 블록 크기 (헤더 + 푸터 포함, 8바이트 정렬)
    size_t extendsize;   // 힙을 확장할 크기 (가용 블록 못 찾았을 때 확장할 크기)
    char *bp;            // 블록 포인터 (payload 시작 위치)

    /* 1. 사용자가 요청한 크기가 0이면 무시하고 NULL 반환 (이상한 요청 방어) */
    if (size == 0)
        return NULL;

    /* 2. 블록 크기 조정: 헤더 + 푸터 + 8바이트 정렬까지 포함한 크기 구하기 */
    if (size <= DSIZE)  // 요청 크기가 8바이트(DSIZE)보다 작으면
        asize = 2 * DSIZE;  // 최소 블록 크기: 헤더(4) + 푸터(4) + 최소 payload(8) = 16바이트
    else  // 요청 크기가 8바이트보다 크면
        // (payload + 헤더(4) + 푸터(4))를 8의 배수로 올림 (정렬 맞추기)
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
        // (size + 8 + 7) / 8 → 올림한 후, 다시 8 곱하기 → 8의 배수

    /* 3. 가용 블록을 찾아서 할당 */
    if ((bp = find_fit(asize)) != NULL) {  // 가용 블록 찾았으면
        place(bp, asize);  // 해당 블록에 메모리 배치 (할당 처리)
        return bp;  // 할당된 블록의 포인터 반환 (payload 시작 위치)
    }

    /* 4. 가용 블록이 없어서 힙 확장 */
    extendsize = MAX(asize, CHUNKSIZE);  // 확장할 크기: 요청 크기 vs 기본 확장 크기(4096바이트) 중 큰 것
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  // 힙을 확장하고 실패하면
        return NULL;  // NULL 반환 (메모리 부족)

    /* 5. 힙 확장 후, 확장된 가용 블록에 메모리 배치 */
    place(bp, asize);  // 확장된 블록에 메모리 배치 (할당 처리)
    return bp;  // 할당된 블록 포인터 반환
}

/* 힙을 words * WSIZE 바이트 만큼 확장하고 새로운 가용 블록 생성 */
static void *extend_heap(size_t words)
{
    char *bp;        // 새로 확장된 가용 블록의 payload 시작 위치
    size_t size;     // 확장할 전체 크기 (바이트 단위)

    /* 1. 짝수 워드로 맞춰서 8바이트 정렬 유지 (블록은 항상 8바이트 배수) */
    // 8바이트를 맞춘다는 얘기임
    // (words가 홀수면 +1 해서 짝수로 맞춤) * WSIZE(4바이트) → byte 크기
    // size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    size = ALIGN(words * WSIZE);

    // 예: words = 5면 → 6 * 4 = 24바이트

    /* 2. mem_sbrk로 힙을 size만큼 확장 (새 공간 시작 주소 bp) */
    if ((long)(bp = mem_sbrk(size)) == -1)  // 힙 확장 실패하면
        return NULL;  // NULL 반환

    /* 3. 새로 확장된 가용 블록의 헤더/푸터 설정 (가용 상태 = 0) */
    // 새로 생긴 블록의 헤더에 (크기 = size, 가용 상태 = 0) 기록
    PUT(HDRP(bp), PACK(size, 0));  
    // 새로 생긴 블록의 푸터에도 똑같이 (크기 = size, 가용 상태 = 0) 기록
    PUT(FTRP(bp), PACK(size, 0));  

    /* 4. 새로운 에필로그 블록 헤더 설정 (크기 = 0, 할당 상태 = 1) */
    // 힙 끝에 있는 에필로그 블록 헤더를 새로 설정 (크기 0, 할당됨)
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    /* 5. 인접 블록이 가용 상태면 병합 (coalesce 호출) */
    // 새로 확장된 블록과 앞에 있던 블록을 병합해서 반환!
    return coalesce(bp);
}


/// coalesce: 인접 블록이 free면 합쳐주기 (boundary tag coalescing)
static void *coalesce(void *bp)  
// bp: 현재 가용 블록의 payload 시작 위치 (병합의 기준 블록!)
{
    // 1. 이전 블록이 할당되었는지 확인 (이전 블록의 푸터를 확인!)
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  
    // → 이전 블록의 푸터에 저장된 할당 여부(1 or 0)를 가져옴!

    // 2. 다음 블록이 할당되었는지 확인 (다음 블록의 헤더를 확인!)
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))) || next_size == 0;

    // → 다음 블록의 헤더에 저장된 할당 여부(1 or 0)를 가져옴!

    // 3. 현재 블록의 크기 가져오기 (헤더에서 크기 읽기)
    size_t size = GET_SIZE(HDRP(bp));  
    int merged = 0;
    // 📌 Case 1: 이전과 다음 블록 모두 할당됨 (병합할 게 없음!)
    if (prev_alloc && next_alloc) {
        return bp;  // 그냥 현재 블록 그대로 반환!
    }

    // 📌 Case 2: 이전 블록은 할당됨, 다음 블록은 가용 (뒤쪽 병합!)
    else if (prev_alloc && !next_alloc) {
        // 2-1. 현재 블록 크기에 다음 블록 크기를 더하기!
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  

        // 2-2. 헤더와 푸터에 병합된 크기와 가용 상태(0)를 기록!
        PUT(HDRP(bp), PACK(size, 0));  // 현재 블록 헤더 업데이트!
        PUT(FTRP(bp), PACK(size, 0));  // 다음 블록 푸터를 현재 블록 푸터로 사용!
        merged = 1;

    }

    // 📌 Case 3: 이전 블록은 가용, 다음 블록은 할당됨 (앞쪽 병합!)
    else if (!prev_alloc && next_alloc) {
        // 3-1. 현재 블록 크기에 이전 블록 크기를 더하기!
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));  

        // 3-2. 이전 블록 헤더에 병합된 크기와 가용 상태(0)를 기록!
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  // 이전 블록 헤더 업데이트!
        PUT(FTRP(bp), PACK(size, 0));  // 현재 블록 푸터를 병합된 블록의 푸터로 사용!

        // 3-3. 병합된 블록의 시작 위치는 이전 블록의 시작 위치!
        bp = PREV_BLKP(bp);  
        merged = 1;

    }

    // 📌 Case 4: 이전과 다음 블록 모두 가용 (앞 + 뒤 병합!)
    else {
        // 4-1. 현재 블록, 이전 블록, 다음 블록 크기를 모두 더하기!
        
        // size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        // 4-2. 이전 블록 헤더, 다음 블록 푸터에 병합된 크기와 가용 상태(0)를 기록!
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));  // 이전 블록 헤더 업데이트!
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));  // 다음 블록 푸터를 병합된 블록 푸터로 사용!

        // 4-3. 병합된 블록의 시작 위치는 이전 블록의 시작 위치!
        bp = PREV_BLKP(bp);  
        merged = 1;
    }
    // 병합이 발생했을 때만 rover를 업데이트

     if (merged) {
        rover = bp;
    }
    // next를 업데이트 해주는 코드 
    //로버를 업데이트 해줘야 함 
    return bp;
}


/*
 * find_fit - find a fit for a block with asize bytes (next-fit search)
 */
// static void *find_fit(size_t asize) {
//     char *bp;

//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
//             return bp;
//         }
//     }
//     return NULL;
// }
static void *find_fit(size_t asize)  // asize: 찾고 싶은 최소 블록 크기 (헤더/푸터 포함)
{
    char *bp;  // bp: 블록 포인터 (payload 시작 위치)

    /* 1. rover(현재 위치)부터 힙 끝까지 탐색 */
    for (bp = rover; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        // 1-1. 현재 블록이 가용 상태 && 크기가 asize 이상이면
        if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)) {
            rover = bp;  // rover 위치를 이 블록으로 업데이트 (next-fit!)
            return bp;   // 찾았으니까 이 블록 포인터 반환! 
        }
    }

    /* 2. 힙 시작(heap_listp)부터 rover 위치까지 다시 탐색 */
    for (bp = heap_listp; bp < rover; bp = NEXT_BLKP(bp)) {
        // 2-1. 현재 블록이 가용 상태 && 크기가 asize 이상이면
        if (!GET_ALLOC(HDRP(bp)) && (GET_SIZE(HDRP(bp)) >= asize)) {
            rover = bp;  // rover 위치를 이 블록으로 업데이트 (next-fit!)
            return bp;   // 찾았으니까 이 블록 포인터 반환!
        }
    }

    /* 3. 못 찾았으면 NULL 반환 */
    return NULL;  // 가용 블록이 없음!
}

/*
 * place - place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)  
// bp: 가용 블록의 시작 주소 (payload 시작 위치)
// asize: 할당할 크기 (헤더 + 푸터 포함, 8의 배수)
{
    size_t csize = GET_SIZE(HDRP(bp));  
    // csize: 현재 가용 블록의 전체 크기 (헤더 + 푸터 포함)

    // [1] 남는 공간이 최소 블록 크기(16바이트) 이상이면 쪼개기!
    if ((csize - asize) >= (2 * DSIZE)) {  
        // 2 * DSIZE = 16바이트 (헤더+푸터 + 최소 payload)

        /* (1-1) 앞부분 asize만큼 할당 처리 */
        PUT(HDRP(bp), PACK(asize, 1));  // 헤더: asize 크기, 할당 상태
        // HDRP 현재 블록의 헤더 위치 / PACK 크기 asize + 할당 상태 1로 저장 
        PUT(FTRP(bp), PACK(asize, 1));  // 푸터: asize 크기, 할당 상태
        // FTRP 현재 블록의 푸터 위치 / PACK 크기 asize + 할당 상태 1로 저장 



        /* (1-2) 남는 공간 → 새로운 가용 블록으로 설정 */
        char *next_bp = NEXT_BLKP(bp);  // 남는 공간의 payload 시작 위치
        PUT(HDRP(next_bp), PACK(csize - asize, 0));  // 헤더: 남은 크기, 가용 상태
        PUT(FTRP(next_bp), PACK(csize - asize, 0));  // 푸터: 남은 크기, 가용 상태
        rover = bp; 
        rover = next_bp;  // ⭐ 쪼개면 남은 블록(next_bp)로 rover 이동 ⭐
    }

    // [2] 남는 공간이 너무 작아서 못 쪼개면 그냥 다 할당!
    else {
        PUT(HDRP(bp), PACK(csize, 1));  // 헤더: 전체 크기, 할당 상태
        PUT(FTRP(bp), PACK(csize, 1));  // 푸터: 전체 크기, 할당 상태
         rover = NEXT_BLKP(bp);   // 전체 쓰고 다음 블록으로 rover 이동

    }
    
}

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */


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
// void *mm_realloc(void *ptr, size_t size)
// {
//     void *newptr;      // 새로 할당할 블록의 포인터
//     size_t copySize;   // 복사할 데이터 크기

//     // [1] 요청 크기가 0이면 → 기존 블록을 free하고 NULL 반환
//     if (size == 0) {
//         mm_free(ptr);  // 기존 블록 해제!
//         return NULL;   // NULL 반환
//     }

//     // [2] 새 크기로 블록을 할당 (malloc!)
//     newptr = mm_malloc(size);
//     if (newptr == NULL)  // 할당 실패 시
//         return NULL;     // NULL 반환

//     // [3] 기존 블록에서 복사할 크기 계산
//     copySize = GET_SIZE(HDRP(ptr)) - DSIZE;
//     // GET_SIZE(HDRP(ptr)): 기존 블록의 전체 크기 (헤더/푸터 포함)
//     // - DSIZE(8): 헤더 + 푸터 크기 빼기 → payload 크기만 남김!

//     // [4] 새 요청 크기보다 크면 → 요청 크기만큼만 복사!
//     // 만약 새 요청 크기가 원래 사이즈보다 작으면!! 
//     if (size < copySize)
//         copySize = size;

//     // [5] 기존 블록의 데이터(payload) → 새 블록으로 복사!
//     memcpy(newptr, ptr, copySize);  // 메모리 복사 (copySize 바이트)

//     // [6] 기존 블록 해제 (free)
//     mm_free(ptr);  // 옛 블록 버리기!

//     // [7] 새 블록 포인터 반환
//     return newptr;
// }

static void remove_node(void *bp)
{
    // 다음 블록 free, 할당 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 현재 블록 크기
    size_t size = GET_SIZE(HDRP(bp));             

    // Case2: 이전 할당, 다음 free인 경우
    if (!next_alloc) {
        // 다음 블록 크기 추가
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));         

        // 병합된 내용을 헤더와, 풋터에 추가
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    
    //  병합 끝난 뒤에, 업데이트
    rover = bp;    
}

void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) {
        // realloc(NULL, size)는 malloc(size)와 같음
        return mm_malloc(size);
    }

    if (size == 0) {
        // realloc(ptr, 0)은 free(ptr) 후 NULL 반환
        mm_free(ptr);
        return NULL;
    }

    size_t oldsize = GET_SIZE(HDRP(ptr)); // 현재 블록 전체 크기 (헤더/푸터 포함)
    size_t asize;

    // 요청 크기를 블록 최소 단위(16바이트)로 맞추기
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    }

    // [1] 새 요청 크기가 기존 블록보다 작거나 같으면 그냥 반환
    if (asize <= oldsize) {
        return ptr;
    }

    // [2] 다음 블록이 free고 합쳐서 충분하면 합치기
    void *next_bp = NEXT_BLKP(ptr);
    if (!GET_ALLOC(HDRP(next_bp)) && GET_SIZE(HDRP(next_bp)) > 0) {
        //  1. coalesce 하기 전에, 원래 데이터 안전하게 복사!
        size_t payload_old = (oldsize >= OVERHEAD) ? oldsize - OVERHEAD : 0;
        char *temp = malloc(payload_old); //  스택 오버플로 방지
        if (temp == NULL) {
            return NULL; // malloc 실패 시 NULL 반환
        }
        memcpy(temp, ptr, payload_old);

        //  2. coalesce
        void *new_bp = coalesce(ptr);
        size_t newsize = GET_SIZE(HDRP(new_bp));

        if (newsize >= asize) {
            PUT(HDRP(new_bp), PACK(newsize, 1));  // 새 블록 헤더 갱신
            PUT(FTRP(new_bp), PACK(newsize, 1));  // 새 블록 푸터 갱신

            //  3. coalesce 끝난 후, 새 블록에 복사!
            if (ptr != new_bp) {
                memcpy(new_bp, temp, payload_old);
            }

            free(temp); //  임시 메모리 해제
            return new_bp;
        }

        free(temp); //  coalesce로 확장해도 실패했으면 메모리 해제
    }

    // [3] 둘 다 안 되면 새로 malloc → 데이터 복사 → old free
    // coalesce(heap_listp);

    void *newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }

    size_t payload_old = (oldsize >= OVERHEAD) ? oldsize - OVERHEAD : 0;
    size_t payload_new = (GET_SIZE(HDRP(newptr)) >= OVERHEAD) ? GET_SIZE(HDRP(newptr)) - OVERHEAD : 0;

    size_t copySize = (payload_old < payload_new) ? payload_old : payload_new;

    memcpy(newptr, ptr, copySize);  // 데이터 복사
    mm_free(ptr);  // 기존 블록 해제

    return newptr;
}





