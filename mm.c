/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * ʹ����ʾ���������Լ���������ԭ�����ռ䣬�����������ַ��������ڶѵ���ʼλ�ü����Կ鿪ͷ��ÿ��
 * �ڳ�ʼ��ʱ��������Ϊ0�������Ŀ������鰴�մ�С�����˳��������дӶ�ʹ�ÿ��������״�����ԭ��ﵽ
 * ���������Ƶ��ڴ����ã�ͨ��ά��һ����������������ά���ѡ�
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Mingyuan Luo",
    /* First member's full name */
    "Mingyuan Luo",
    /* First member's email address */
    "18300240005@fudan.edu.cn",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size)+(ALIGNMENT-1))&~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x,y) ((x)>(y)?(x):(y))
#define PACK(size, alloc) ((size)|(alloc))
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p)=(val))
#define GET_SIZE(p) (GET(p)&~0x7)
#define GET_ALLOC(p) (GET(p)&0x1)
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp)+GET_SIZE(HDRP(bp))-DSIZE)
#define NEXT_BLKP(bp) ((char *)(bp)+GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))
#define PREV_POI(bp) ((char *)bp)
#define NEXT_POI(bp) ((char *)(bp)+WSIZE)
#define PREV(bp) (*(char **)(bp))
#define NEXT(bp) (*(char **)(NEXT_POI(bp)))
#define LINK(p, ptr) (*(unsigned int *)(p)=(unsigned int)(ptr))
#define LIST_ARRAY(ptr, index) *((char **)ptr+index)
#define LIST_NUM 16

static char *heap_listp;
static void *free_lists;

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void *place(void *bp, size_t asize);
static void insert_list(void *bp, size_t block_size);
static void pop_list(void *bp);

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;
    size=(words%2)?(words+1)*WSIZE:words*WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    insert_list(bp, size);
    return coalesce(bp);
}

static void *find_fit(size_t asize) {
    size_t size = asize;
    void *list_ptr = NULL;
    for(int i=0;i < LIST_NUM;i++) {
        if ((i==LIST_NUM-1) || ((size<=1) && (LIST_ARRAY(free_lists, i)!= NULL))) {
            list_ptr  = LIST_ARRAY(free_lists, i);
            while ((list_ptr != NULL) && (asize > GET_SIZE(HDRP(list_ptr))))
                list_ptr = PREV(list_ptr);
            if (list_ptr != NULL)
                break;
        }
        size >>= 1;
    }
    return list_ptr;
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc) {
        return bp;
    } else if (prev_alloc && !next_alloc) {
        pop_list(bp);
        pop_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        pop_list(bp);
        pop_list(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        pop_list(PREV_BLKP(bp));
        pop_list(bp);
        pop_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insert_list(bp, size);
    return bp;
}

static void insert_list(void *bp, size_t size) {
    void *list_ptr = NULL;
    void *insert_loc = NULL;
    int i = 0;
    for(; (i < (LIST_NUM - 1)) && (size > 1); i++) {
        size = size >> 1;
    }
    list_ptr = LIST_ARRAY(free_lists, i);
    while ((list_ptr != NULL) && (size > GET_SIZE(HDRP(list_ptr)))) {
        insert_loc = list_ptr;
        list_ptr = PREV(list_ptr);
    }
    if (list_ptr) {
        if (insert_loc) {
            LINK(PREV_POI(insert_loc), bp);
            LINK(NEXT_POI(bp), insert_loc);
            LINK(PREV_POI(bp), list_ptr);
            LINK(NEXT_POI(list_ptr), bp);
        } else {
            LINK(NEXT_POI(list_ptr), bp);
            LINK(PREV_POI(bp), list_ptr);
            LINK(NEXT_POI(bp), NULL);
            LIST_ARRAY(free_lists, i)=bp;
        }
    } else {
        if (insert_loc) {
            LINK(NEXT_POI(bp), insert_loc);
            LINK(PREV_POI(insert_loc), bp);
            LINK(PREV_POI(bp), NULL);
        } else {
            LIST_ARRAY(free_lists, i)= bp;
            LINK(PREV_POI(bp), NULL);
            LINK(NEXT_POI(bp), NULL);
            return;
        }
    }
}

static void pop_list(void *bp) {
    int i = 0;
    size_t size = GET_SIZE(HDRP(bp));
    if (NEXT(bp) == NULL) {
        for(; i<(LIST_NUM - 1) && size>1; i++)
            size = size >> 1;
        LIST_ARRAY(free_lists, i)= PREV(bp);
        if (LIST_ARRAY(free_lists, i) != NULL)
            LINK(NEXT_POI(LIST_ARRAY(free_lists, i)), NULL);
        return;
    }
    LINK(PREV_POI(NEXT(bp)), PREV(bp));
    if (PREV(bp) != NULL) {
        LINK(NEXT_POI(PREV(bp)), NEXT(bp));
    }
}

static void *place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    void *np = NULL;
    pop_list(bp);
    if ((csize - asize) >= (2*DSIZE)) {
        if ((csize - asize) >= 200) {
            PUT(HDRP(bp), PACK(csize - asize, 0));
            PUT(FTRP(bp), PACK(csize - asize, 0));
            np = NEXT_BLKP(bp);
            PUT(HDRP(np), PACK(asize, 1));
            PUT(FTRP(np), PACK(asize, 1));
            insert_list(bp, csize - asize);
            return np;
        } else {
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            np = NEXT_BLKP(bp);
            PUT(HDRP(np), PACK(csize - asize, 0));
            PUT(FTRP(np), PACK(csize - asize, 0));
            insert_list(np, csize - asize);
        }
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    return bp;
}

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    int i;
    free_lists = mem_sbrk(LIST_NUM*WSIZE);
    for (i = 0; i < LIST_NUM; i++) {
        LIST_ARRAY(free_lists, i)= NULL;
    }
    if ((heap_listp = mem_sbrk(4*WSIZE))==(void *) -1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));
    PUT(heap_listp + (3*WSIZE), PACK(0,1));
    heap_listp += (2*WSIZE);
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extendsize;
    char *bp;
    char *ptr;
    if (!size)
        return NULL;
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE*((size+(DSIZE)+(DSIZE-1))/DSIZE);
    if ((bp = find_fit(asize)) != NULL) {
        ptr =  place(bp, asize);
        return ptr;
    }
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    ptr =  place(bp, asize);
    return ptr;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    insert_list(bp, size);
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    void *oldptr = ptr;
    void *new_block;
    void *nextptr;
    size_t oldSize, asize;
    if (!size) {
        mm_free(oldptr);
        return NULL;
    }
    if (!oldptr)
        return mm_malloc(size);
    asize = ALIGN(size);
    oldSize =GET_SIZE(HDRP(oldptr))-DSIZE;
    if (asize == oldSize)
        return oldptr;
    if (asize < oldSize) {
        if (oldSize-asize<=2*DSIZE)
            return oldptr;
        PUT(HDRP(oldptr), PACK(asize + DSIZE, 1));
        PUT(FTRP(oldptr), PACK(asize + DSIZE, 1));
        new_block = oldptr;
        oldptr = NEXT_BLKP(new_block);
        PUT(HDRP(oldptr), PACK(oldSize - asize, 0));
        PUT(FTRP(oldptr), PACK(oldSize - asize, 0));
        insert_list(oldptr, GET_SIZE(HDRP(oldptr)));
        coalesce(oldptr);
        return new_block;
    }
    nextptr = NEXT_BLKP(oldptr);
    if (!GET_ALLOC(HDRP(nextptr))) {
        int nextSize = GET_SIZE(HDRP(nextptr));
        if (nextSize + oldSize >= asize) {
            pop_list(nextptr);
            if (nextSize + oldSize - asize <= DSIZE) {
                PUT(HDRP(oldptr), PACK(oldSize + DSIZE + nextSize, 1));
                PUT(FTRP(oldptr), PACK(oldSize + DSIZE + nextSize, 1));
                return oldptr;
            } else {
                PUT(HDRP(oldptr), PACK(asize + DSIZE, 1));
                PUT(FTRP(oldptr), PACK(asize + DSIZE, 1));
                new_block = oldptr;
                oldptr = NEXT_BLKP(new_block);
                PUT(HDRP(oldptr), PACK(oldSize + nextSize - asize, 0));
                PUT(FTRP(oldptr), PACK(oldSize + nextSize - asize, 0));
                insert_list(oldptr, GET_SIZE(HDRP(oldptr)));
                coalesce(oldptr);
                return new_block;
            }
        }
    }
    if((new_block = mm_malloc(size))==NULL)
        return NULL;
    memcpy(new_block, oldptr, oldSize);
    mm_free(oldptr);
    return new_block;
}
