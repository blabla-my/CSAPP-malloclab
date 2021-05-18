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

/* judge if a chunk suits a request */
#define LEGAL(bp,size)  ( !GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= (size) )

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(HDRP(bp)-WSIZE))

/* operation of link list */
#define next(bp)        ((char*)(GET(bp)))
#define prev(bp)        ((char*)(GET((char*)(bp)+WSIZE)))
#define set_next(bp,n)  (PUT((bp),(unsigned int)(n)))
#define set_prev(bp,p)  (PUT( (char*)(bp) + 4,(unsigned int)(p) ))

/* structure and data of lists */
#define MAX_LISTS 64
#define IDX(bp) ((GET_SIZE(HDRP(bp))-WSIZE) >> 3)  
typedef struct {
    unsigned int hdr;
    char * next;
    char * prev;
    unsigned int ftr;
} head_chunk;

static head_chunk head_chunks[MAX_LISTS];
static char* heap_listp[MAX_LISTS];
//static char* pre_loc[MAX_LISTS];

/*
 * extend_heap - 
 */
static void *coalesce(void * bp);

static void insert_free_list(void * bp){
    if(bp){
        int idx = IDX(bp) < MAX_LISTS ? IDX(bp) : 0 ;
        //printf("insert request %p[%d], at idx(%d)\n",bp,GET_SIZE(HDRP(bp)),idx);
        /* insert the block to heap_listp[idx] */
        char * _next = next(heap_listp[idx]);
        /* set pointer of head */
        set_next(heap_listp[idx],bp);
        /* set pointer of bp */
        set_next(bp,_next);
        set_prev(bp,heap_listp[idx]);
        /* set pointer of _next */
        set_prev(_next,bp);
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

        /* update pre_loc */
        /*
        if(pre_loc == bp){
            pre_loc = _next;   
        }
        */
    }
}

static void * extend_heap(size_t words){
    char * bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = words % 2 ? (words + 1)*WSIZE : words*WSIZE ;
    if((long) (bp = mem_sbrk(size)) == -1) {
        //printf("?\n");
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
        insert_free_list(bp);
        return bp;
    }

    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        char * next_blkp = NEXT_BLKP(bp);
        PUT(HDRP(bp),PACK(size,0));
        PUT(FTRP(bp),PACK(size,0));
        /* maintain the free list */
        unlink_free_list(next_blkp);
        insert_free_list(bp);
    }

    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
        bp = PREV_BLKP(bp);
        /* maintain the free list */
        unlink_free_list(bp);
        insert_free_list(bp);
    }

    else {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        /* unlink next chunk of implicit link on link */
        unlink_free_list(NEXT_BLKP(bp));
        unlink_free_list(PREV_BLKP(bp));
        bp = PREV_BLKP(bp);
        insert_free_list(bp);
    }
    
    return bp;
}

static void split(void * bp , size_t asize, int alloc){
    size_t size = GET_SIZE(HDRP(bp));
    char * ftr = FTRP(bp);
    //printf("split request %p[%d] [%d]\n",bp,size,asize);

    /* determine asize */
    asize = (size - asize <= DSIZE) ? size : asize ;

    /* set the size of new chunk */
    PUT(HDRP(bp), PACK(asize,alloc));
    PUT(FTRP(bp), PACK(asize,alloc));

    /* split the left chunk */
    if( size - asize > DSIZE ){
        size_t left_size = size - asize;
        char * hdr = ftr + WSIZE - left_size ; 
        PUT(hdr, PACK(left_size,0));
        PUT(ftr, PACK(left_size,0));
        /* insert the left chunk to the free list */
        coalesce((char*)(hdr+WSIZE));
    }
}


/*
 * place - 
 *
 */
static void place(void *bp, size_t asize){
    if(GET_ALLOC(HDRP(bp))) return ;

    unlink_free_list(bp);
    split(bp,asize,1);
}


/*
 * find_fit - search a suitable free chunk according to specific strategy
 */
/*
static void * next_fit(size_t asize){
    char * bp;
    for(bp = pre_loc ; bp != heap_listp; bp = next(bp)){
        if(LEGAL(bp,asize)){
            return bp;
        }
    }
    for(bp = next(heap_listp) ; bp != pre_loc; bp = next(bp)){
        if(LEGAL(bp,asize)){
            return bp;
        }
    }
    return NULL;
}
*/
static void * first_fit(size_t asize){
    char * bp;
    for(bp = next(heap_listp[0]) ; bp != heap_listp[0] ; bp = next(bp)){
        if(LEGAL(bp,asize)){
            return bp;
        }
    }
    return NULL;
}

static void * find_fit(size_t asize){
    int idx = (asize >>3) < MAX_LISTS ? (asize >> 3) : 0;
    if(idx){
        if( next(heap_listp[idx]) != heap_listp[idx] ){
            return next(heap_listp[idx]);
        }
    }
    return first_fit(asize);
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
    
    for(int i=0;i<MAX_LISTS;i++){
        heap_listp[i] = (char*)&(head_chunks[i]) + WSIZE;
        head_chunks[i].hdr = head_chunks[i].ftr = PACK(8,1);
        set_next(heap_listp[i],heap_listp[i]);
        set_prev(heap_listp[i],heap_listp[i]);
    }
    //printf("heap_listp init down.\n");
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if(extend_heap(CHUNKSIZE / WSIZE) == NULL){
        return -1;
    }
    //printf("mem_init down.\n");
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
    /*if(size>>3 < MAX_LISTS){
        insert_free_list(ptr);
        return ;
    }*/
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    //printf("mm_realloc request %p[%d]\n",ptr,size);
    void *oldptr = ptr;
    void *newptr;
    size_t asize,oldsize;
    
    /* do some check */
    if(size == 0) return NULL;
    if(ptr == NULL) return mm_malloc(size);

    /* get size */
    asize = ALIGN(size) + DSIZE;
    oldsize = GET_SIZE(HDRP(ptr));
    
    /* new size <= old size */
    if(asize <= oldsize){
        split(ptr,asize,1);
        return ptr;
    }

    /* new size > old size*/
    char * nblk = NEXT_BLKP(ptr);
    size_t nsize = GET_SIZE(HDRP(nblk));
    /* plus next block can fit the request size */
    if(!GET_ALLOC(HDRP(nblk)) && oldsize + nsize >= asize ){
        size = nsize + oldsize; 
        /* coalesce two chunk */
        unlink_free_list(nblk);
        /* set the size */
        PUT(HDRP(ptr),PACK(size, 1));
        PUT(FTRP(ptr),PACK(size, 1));
        /* if neccessary, split */
        split(ptr, asize, 1);
        return ptr;
    }

    /* need to allocate new block to fit the request size */
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    memcpy(newptr, oldptr, oldsize-DSIZE);
    mm_free(oldptr);
    return newptr;
}








