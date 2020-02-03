/*
 * mm.c - The fastest, least memory-efficient malloc package.
 * 
 * In this approach, I implemented Segregated free lists using an array of pointers.
 * each pointer represent a bin of a class of a specified size.
 * the free lists within each bin ordered by size in increasing order.
 * INSERTION POLICY is address-ordered, and FINDING POLICY is best fit.
 * 
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

    "105179657",

    "Karim",

    "Benlghalia",

    "",

    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
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

#define PREVPTR(bp) ((char *)(bp))
#define NEXTPTR(bp) ((char *)(bp) + WSIZE)
/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* Function prototypes */
static void *extend_heap(size_t dwords);
static void *coalesce(void *bp);
static void *find_fit(size_t size);
static void place(void *bp, size_t asize);
void ADD_LIST(char *p);
void DELETEBLOK(char *p);
inline char *get_classPtr(size_t size);
static void insert(char *p, char *pre, char *head, char *nextp);
void checkheap(int testT);
static void printblock(void *ptr);
static void checkblock(void *ptr);

/* Global variables */
static char *heap_listp = NULL;
static char *Arr_list = NULL;

/****************************************************************/
/* 
 * mm_init - initialize the malloc package.
 */

int mm_init(void)
{
    if ((heap_listp = mem_sbrk(20 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);
    PUT(heap_listp + (1 * WSIZE), 0);
    PUT(heap_listp + (2 * WSIZE), 0);
    PUT(heap_listp + (3 * WSIZE), 0);
    PUT(heap_listp + (4 * WSIZE), 0);
    PUT(heap_listp + (5 * WSIZE), 0);
    PUT(heap_listp + (6 * WSIZE), 0);
    PUT(heap_listp + (7 * WSIZE), 0);
    PUT(heap_listp + (8 * WSIZE), 0);
    PUT(heap_listp + (9 * WSIZE), 0);
    PUT(heap_listp + (10 * WSIZE), 0);
    PUT(heap_listp + (11 * WSIZE), 0);
    PUT(heap_listp + (12 * WSIZE), 0);
    PUT(heap_listp + (13 * WSIZE), 0);
    PUT(heap_listp + (14 * WSIZE), 0);
    PUT(heap_listp + (15 * WSIZE), 0);

    PUT(heap_listp + (16 * WSIZE), 0);              /* Alignment padding */
    PUT(heap_listp + (17 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (18 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (19 * WSIZE), PACK(0, 1));     /* Epilogue header */

    Arr_list = heap_listp;
    heap_listp += (18 * WSIZE);
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if ((extend_heap(CHUNKSIZE / DSIZE)) == NULL)
        return -1;
    //checkheap(1);
    //checkheap_list(1);
    return 0;
}

/**
 * Return a matched pointer of the size from the array of bins 
 *
*/
inline char *get_classPtr(size_t size)
{
    int i;

    if (size <= 16)
        i = 0;
    else if (size <= 24)
        i = 1;
    else if (size <= 36)
        i = 2;
    else if (size <= 48)
        i = 3;
    else if (size <= 56)
        i = 4;
    else if (size <= 72)
        i = 5;
    else if (size <= 80)
        i = 6;
    else if (size <= 96)
        i = 7;
    else if (size <= 104)
        i = 8;
    else if (size <= 128)
        i = 9;
    else if (size <= 256)
        i = 10;
    else if (size <= 512)
        i = 11;
    else if (size <= 1024)
        i = 12;
    else if (size <= 2048)
        i = 13;
    else if (size <= 4096)
        i = 14;
    else
    {
        i = 15;
    }

    return Arr_list + (i * WSIZE);
}

/*
 ********************* coalesce**********************************
 
 */

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    {
        /* Case 1 */
    }
    else if (prev_alloc && !next_alloc)
    { /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        DELETEBLOK(NEXT_BLKP(bp)); /*remove the next block*/
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc)
    { /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        DELETEBLOK(PREV_BLKP(bp)); /*remove the prev block*/
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else
    { /* Case 4 */
        size += GET_SIZE(FTRP(NEXT_BLKP(bp))) + GET_SIZE(HDRP(PREV_BLKP(bp)));
        DELETEBLOK(PREV_BLKP(bp));
        DELETEBLOK(NEXT_BLKP(bp));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    ADD_LIST(bp);
    return bp;
}
/*
 ********************* insert helper **********************************
 
 */

static void insert(char *p, char *pre, char *head, char *nextp)
{

    if (pre == head)
    {
        PUT(head, p);
        PUT(NEXTPTR(p), nextp);
        PUT(PREVPTR(p), NULL);
        if (nextp != NULL)
            PUT(PREVPTR(nextp), p);
    }
    else
    {
        PUT(NEXTPTR(pre), p);
        PUT(PREVPTR(p), pre);
        PUT(NEXTPTR(p), nextp);
        if (nextp != NULL)
            PUT(PREVPTR(nextp), p);
    }
}

/*
 ********************* ADDLIST**********************************
 
 */

inline void ADD_LIST(char *p)
{
    char *head = get_classPtr(GET_SIZE(HDRP(p)));
    char *nextp;
    char *prevp = head;

    for (nextp = GET(head); nextp != NULL; nextp = GET(NEXTPTR(nextp)))
    {
        if (GET_SIZE(HDRP(nextp)) < GET_SIZE(HDRP(p)))
            ;
        else
        {
            break;
        }
        prevp = nextp;
    }

    insert(p, prevp, head, nextp);
}

/*
 ********************* DELETEBLOK**********************************
 
 */

inline void DELETEBLOK(char *p)
{
    char *head = get_classPtr(GET_SIZE(HDRP(p)));

    if (GET(PREVPTR(p)) != NULL)
    {
        if (GET(NEXTPTR(p)) != NULL)
        {
            PUT(PREVPTR(GET(NEXTPTR(p))), GET(PREVPTR(p)));
            PUT(NEXTPTR(GET(PREVPTR(p))), GET(NEXTPTR(p)));
            PUT(NEXTPTR(p), NULL);
            PUT(PREVPTR(p), NULL);
        }
        else
        {
            PUT(NEXTPTR(GET(PREVPTR(p))), GET(NEXTPTR(p)));
            PUT(NEXTPTR(p), NULL);
            PUT(PREVPTR(p), NULL);
        }
    }
    else
    {
        if (GET(NEXTPTR(p)) != NULL)
        {
            PUT(PREVPTR(GET(NEXTPTR(p))), 0);
            PUT(head, GET(NEXTPTR(p)));
            PUT(NEXTPTR(p), NULL);
            PUT(PREVPTR(p), NULL);
        }

        else
        {
            PUT(head, GET(NEXTPTR(p)));
            PUT(NEXTPTR(p), NULL);
            PUT(PREVPTR(p), NULL);
        }
    }
}
/*
 ********************* FIND FIT**********************************
 
 */

static void *find_fit(size_t size)
{
    /*First fit is the best*/

    char *head = get_classPtr(size);

    while (head != (heap_listp - (2 * WSIZE))) // we need to earch witin all the bins starting from the matched bin. (heap_listp - (2 * WSIZE)) is the end of bin's array
    {
        char *tmpP;
        for (tmpP = GET(head); tmpP != NULL; tmpP = GET(NEXTPTR(tmpP)))
        {

            if (GET_SIZE(HDRP(tmpP)) >= size)
                return tmpP;
        }
        head += WSIZE;
    }
    return NULL;
}
/*
 ********************* Extend heap**********************************
 
 */

static void *extend_heap(size_t dwords)
{
    char *bp;
    size_t size;
    /* Allocate an even number of words to maintain 16 bytes alignment */
    size = (dwords % 2) ? (dwords + 1) * DSIZE : dwords * DSIZE;

    if ((long)(bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */

    /*init the prev and next free pointer fields*/
    PUT(NEXTPTR(bp), NULL);
    PUT(PREVPTR(bp), NULL);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    return coalesce(bp); /* Coalesce if the previous block was free */
}

/*
 ********************* Place**********************************
 
 */

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) < (2 * DSIZE))
    {
        DELETEBLOK(bp); /*remove from free list*/
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    else
    {
        DELETEBLOK(bp); /*remove from free list*/
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));

        PUT(NEXTPTR(bp), 0);
        PUT(PREVPTR(bp), 0);
        coalesce(bp);
    }
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
    if (size == 0)
        return NULL;

    if (size <= DSIZE)
    {
        asize = 2 * (DSIZE);
    }
    else
    {
        asize = (DSIZE) * ((size + (DSIZE) + (DSIZE - 1)) / (DSIZE));
    }

    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / DSIZE)) == NULL)
    {
        return NULL;
    }
    place(bp, asize);
    return bp;
}
/*
 * mm_free - Freeing a block does nothing.
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
    size_t asize = MAX(ALIGN(size) + DSIZE, 16);
    size_t Old_size = GET_SIZE(HDRP(ptr)); //Get the size of the old block

    void *bp;
    char *next = HDRP(NEXT_BLKP(ptr));
    size_t newsize = Old_size + GET_SIZE(next); //combine the old size with the size of the

    if (ptr == NULL)
        return mm_malloc(size); // if ptr is null it is just a malloc

    if (size == 0) //if size is 0, then it is just free and return null.
    {
        mm_free(ptr);
        return NULL;
    }

    if (asize == Old_size) //If the size of the old block and requested size are same then return the old block pointer
        return ptr;

    if (asize > Old_size)
    {

        if (!GET_ALLOC(next) && newsize >= asize) //if next bloc is not allocated and the combined size is sufficient to hold asize
        {

            DELETEBLOK(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(asize, 1));
            PUT(FTRP(ptr), PACK(asize, 1));
            bp = NEXT_BLKP(ptr);
            PUT(HDRP(bp), PACK(newsize - asize, 1));
            PUT(FTRP(bp), PACK(newsize - asize, 1));
            mm_free(bp);
            return ptr;
        }

        bp = mm_malloc(asize);
        memcpy(bp, ptr, Old_size);
        mm_free(ptr);
        return bp;
    }

    else
    {

        bp = mm_malloc(asize);
        memcpy(bp, ptr, asize);
        mm_free(ptr);
        return bp;
    }
}
/*
 ********************* PRINTBLOCK **********************************
 
 */

static void printblock(void *bp)
{

    //checkheap(0);
    size_t header_size = GET_SIZE(HDRP(bp));
    size_t header_alloc = GET_ALLOC(HDRP(bp));
    size_t footer_size = GET_SIZE(FTRP(bp));
    size_t footer_alloc = GET_ALLOC(FTRP(bp));

    if (header_size == 0)
    {
        printf("%p: EOL\n", bp);
        return;
    }
    char a = header_alloc ? 'a' : 'f';
    char b = footer_alloc ? 'a' : 'f';
    printf("%p: header: (%d:%c) footer: (%d:%c)\n", bp,
           header_size, a,
           footer_size, b);
}

/*
 ********************* CHECKBLOCK**********************************
 
 */

static void checkblock(void *bp)
{
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}

/* 
 * checkheap - Minimal check of the heap for consistency 
 */
void checkheap(int testT)
{

    char *bp = heap_listp;

    if (testT)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (testT)
            printblock(bp);
        checkblock(bp);
    }

    if (testT)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}

void checkheap_list(int testT)
{

    char *head = Arr_list;

    while (head != (heap_listp - (2 * WSIZE))) // we need to earch witin all the bins starting from the matched bin. (heap_listp - (2 * WSIZE)) is the end of bin's array
    {
        if (testT)
            printf("Heap (%p):\n", head);
        if ((GET_SIZE(HDRP(head)) != DSIZE) || !GET_ALLOC(HDRP(head)))
            printf("Bad prologue header\n");
        checkblock(head);
        char *tmpP;
        for (tmpP = GET(head); tmpP != NULL; tmpP = GET(NEXTPTR(tmpP)))
        {
            if (tmpP)
                printblock(tmpP);
            checkblock(tmpP);

            if (testT)
                printblock(tmpP);
            if ((GET_SIZE(HDRP(tmpP)) != 0) || !(GET_ALLOC(HDRP(tmpP))))
                printf("Bad epilogue header\n");
        }
        head += WSIZE;
    }
}
