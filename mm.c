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
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

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
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1<<12)

#define MAX(x,y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size , alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)          (*(unsigned int *)(p))
#define PUT(p,val)      (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) &  0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(HDRP(bp)-WSIZE))

/* operation of link list */
#define next(bp)        ((char*)(GET(bp)))
#define prev(bp)        ((char*)(GET((char*)(bp)+WSIZE)))
#define set_next(bp,n)  (PUT((bp),(unsigned int)(n)))
#define set_prev(bp,p)  (PUT( (char*)(bp) + 4,(unsigned int)(p) ))

static void* head_chunk[4]={NULL,NULL,NULL,NULL};
static char* heap_listp = (char*)(&head_chunk[2]);
/*
 * extend_heap - 
 */
static void *coalesce(void * bp);

static void insert_free_list(char * listp, void * bp){
    if(listp && bp){
        //printf("insert free list request: [%d].\n", GET_SIZE(HDRP(bp)));
        char * _next = next(listp);

        /* set pointer of bp */
        set_next(bp,_next);
        set_prev(bp,listp);
        /* set pointer of _next */
        set_prev(_next,bp);
        /* set pointer of heap_listp */
        set_next(listp,bp);
        //printf("insert free list: [%d] down.\n", GET_SIZE(HDRP(bp)));
    }
}

static void unlink_free_list(void *bp){
    if(bp){
        //printf("unlink request %p[%d]\n",bp,GET_SIZE(HDRP(bp)));
        char *_prev,*_next;
        _prev = prev(bp);
        _next = next(bp);
        /* set pointer of _prev */
        set_next(_prev,_next);
        /* set pointer of _next */
        set_prev(_next,_prev);
    }
}

static void * extend_heap(size_t words){
    char * bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = words % 2 ? (words + 1)*WSIZE : words*WSIZE ;
    if((long) (bp = mem_sbrk(size)) == -1) {
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));
    /* Coalesce if the previous/next block was free */
    bp = coalesce(bp);
    return bp;
}

/*
 * coalesce - unlink at the same time
 */

static void *coalesce(void * bp){
    //printf("coalesce bp : %p [%d]\n", bp,GET_SIZE(HDRP(bp)));
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    if(prev_alloc && next_alloc){
        insert_free_list(heap_listp,bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        char *_prev,*_next;
        _prev = prev(NEXT_BLKP(bp));
        _next = next(NEXT_BLKP(bp));
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
        /* pointer of _prev */
        set_next(_prev,bp);
        /* pointer of _next */
        set_prev(_next,bp);
        /* pointer of bp */
        set_next(bp,_next);
        set_prev(bp,_prev);
    }

    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
        bp = PREV_BLKP(bp);
    }

    else {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        /* unlink next chunk of implicit link on link */
        unlink_free_list(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
    }
    
    return bp;
}

/*
 * place - 
 *
 */

static void place(void *bp, size_t asize){
    if(GET_ALLOC(HDRP(bp))) return ;

    size_t size = GET_SIZE(HDRP(bp));
    char *ftr = FTRP(bp);

    /* determine asize */
    asize = (size-asize <= DSIZE) ? size : asize ; 

    /* unlink the chunk */
    unlink_free_list(bp);
    
    /* set the header and footer of the new chunk */
    PUT(HDRP(bp), PACK(asize,1));
    PUT(FTRP(bp), PACK(asize,1));

    /* split the old chunk */
    if( size - asize > DSIZE ){
        size_t left_size = size - asize;
        char * hdr = ftr + WSIZE - left_size ; 
        PUT(hdr, PACK(left_size,0));
        PUT(ftr, PACK(left_size,0));
        /* insert the left chunk to the free list */
        insert_free_list(heap_listp, (char*)(hdr+WSIZE));
    }
}


/*
 * find_fit - search a suitable free chunk according to specific strategy
 */

static void * find_fit(size_t asize){
    /*
    * a simplest version
    * search the implicit linklist of chunk from the headlistp
    * using first fit
    */
    static char * bp ; 
    bp= next(heap_listp) ;
    //printf("[%d] #%d\n",GET_SIZE(bp),GET_ALLOC(bp));
    for(; bp != heap_listp && ( GET_ALLOC(HDRP(bp)) || GET_SIZE(HDRP(bp)) < asize ) ; bp = next(bp)) {
    };
    //printf("[%d] #%d\n",GET_SIZE(HDRP(bp)),GET_ALLOC(HDRP(bp)));
    if( bp != heap_listp && GET_SIZE(HDRP(bp)) >= asize && !GET_ALLOC(HDRP(bp))){
        //printf("find fit [%d] succ.\n",asize);
        return bp;
    }
    return NULL;
}


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    char * start;
    if((start = mem_sbrk(4*WSIZE)) == (void*)-1){
        return -1;
    }
    PUT(start, 0);
    PUT(start + 1*WSIZE, PACK(8,1));
    PUT(start + 2*WSIZE, PACK(8,1));
    PUT(start + 3*WSIZE, PACK(0,1));

    /* initialize the heap_listp */
    set_next(heap_listp,heap_listp);
    set_prev(heap_listp,heap_listp);

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if(extend_heap(CHUNKSIZE / WSIZE) == NULL){
        return -1;
    }
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    /* Ignore spurious requests */
    if ( size == 0){
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs */
    asize = ALIGN(size) + DSIZE;
    //printf("alloc request [%d]\n",asize);
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL){
        place(bp,asize);
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    //printf("alloc [%d] down\n",asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    //printf("mm_free request %p[%d]\n",ptr,GET_SIZE(HDRP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size,0));
    PUT(FTRP(ptr), PACK(size,0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}








