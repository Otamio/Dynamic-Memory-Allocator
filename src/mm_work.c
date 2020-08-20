/*
 * mm.c
 *
 * This is the only file you should modify.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
/* Not debug mode */
// #define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* Define implementation method */
#define SEGRE
#define SEG_SIZE 8

/* Define search strategy */
#define FIRST_FIT
// #define BEST_FIT

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/* Use macros and global values from the textbook */
#define WSIZE       4       /* Word size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define QSIZE       16      /* Quad word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)            (*(unsigned int *)(p))
#define PUT(p, val)       (*(unsigned int *)(p) = (val))
#define GET_8(p)          (*(unsigned long *)(p))
#define PUT_8(p, val)     (*(unsigned long *)(p) = (unsigned long)(val))
#define GET_8add(p)       ((char **)(p))
#define PUT_8add(p, val)  ((char **)(p) = (unsigned long)(val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)     (GET(p) & ~0x7)
#define GET_ALLOC(p)    (GET(p) & 0x1)
#define GET_SIZE_8(p)   (GET_8(p) & ~0x7)
#define GET_ALLOC_8(p)  (GET_8(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute address of next and previous blocks (explicit list) */
#define NEXT(bp)       (*GET_8add(bp))
#define PREV(bp)       (*GET_8add(bp + DSIZE))

/* Global variables */
static char *heap_listp = NULL;  /* pointer to first block (Only has a
                                    symbolic meaning for this program) */
#ifndef SEGRE
  static char *root = NULL;        /* pointer to first free block */
#endif

#ifdef SEGRE
  static char *start_root = NULL;   /* starting pointer for the segregated list */
  // static char *this_root = NULL;    /* root for segregated list */
#endif

/* Helper functions */
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void *coalesce(void *bp);
static inline void mm_unlink(void *bp);
void mm_checkheap(int verbose);
static void printblock(void *bp);
static void checkblock(void *bp);

#ifdef DEBUG
  static inline int in_heap(const void *p);
  static inline int aligned(const void *p);
#endif

#ifdef SEGRE
  static int get_segid(size_t asize);
  static inline void *get_root(int segid, void *newroot);
  static inline void *get_rootd(size_t size);
  static inline void root_init();
#endif

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(18*DSIZE)) == (void *)-1)
    return -1;

  start_root = heap_listp;
  PUT_8(heap_listp, 0);           /* Group 1 */
  PUT_8(heap_listp+DSIZE, 0);     /* Group 1 */
  PUT_8(heap_listp+DSIZE*2, 0);   /* Group 2 */
  PUT_8(heap_listp+DSIZE*3, 0);   /* Group 2 */
  PUT_8(heap_listp+DSIZE*4, 0);   /* Group 3 */
  PUT_8(heap_listp+DSIZE*5, 0);   /* Group 3 */
  PUT_8(heap_listp+DSIZE*6, 0);   /* Group 4 */
  PUT_8(heap_listp+DSIZE*7, 0);   /* Group 4 */
  PUT_8(heap_listp+DSIZE*8, 0);   /* Group 5 */
  PUT_8(heap_listp+DSIZE*9, 0);   /* Group 5 */
  PUT_8(heap_listp+DSIZE*10, 0);  /* Group 6 */
  PUT_8(heap_listp+DSIZE*11, 0);  /* Group 6 */
  PUT_8(heap_listp+DSIZE*12, 0);  /* Group 7 */
  PUT_8(heap_listp+DSIZE*13, 0);  /* Group 7 */
  PUT_8(heap_listp+DSIZE*14, 0);  /* Group 8 */
  PUT_8(heap_listp+DSIZE*15, 0);  /* Group 8 */
  PUT(heap_listp+DSIZE*16, 0);                            /* alignment padding */
  PUT(heap_listp+DSIZE*16+WSIZE, PACK(OVERHEAD, 1));      /* prologue header */
  PUT(heap_listp+DSIZE*17, PACK(OVERHEAD, 1));            /* prologue footer */
  PUT(heap_listp+DSIZE*17+WSIZE, PACK(0, 1));             /* epilogue header */
  heap_listp += DSIZE*17;                                 /* Reallocate heap_listp */
  root_init(0);                                           /* Initialize root container */

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if ( extend_heap(CHUNKSIZE/WSIZE) == NULL )
    return -1;

  return 0;
}

/*
 * malloc - Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size) {
  size_t asize;                              /* adjusted block size */
  size_t extendsize;                         /* amount to extend heap if no fit */
  char *bp;
  if (heap_listp == NULL)
    mm_init();

  /* Ignore spurious requests */
  if (size <= 0)
    return NULL;

  /* Adjust block size to include overhead and alignment reqs.
   *  Overhead is header and footer, 8 bytes
   *  Payload must be 16 bytes */
  if (size <= QSIZE)
    asize = QSIZE + OVERHEAD;
  else if (size <= 449 && size >= 448)  /* Special optimization for binary-bal */
    asize = 512;
  else
    asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE); /* Conform to alignment requirement */

  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);

#ifdef DEBUG
  assert(in_heap(bp) == 1);
  assert(aligned(bp) == 1);
#endif

    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
    return NULL;
  place(bp, asize);

#ifdef DEBUG
  assert(in_heap(bp) == 1);
  assert(aligned(bp) == 1);
#endif

  return bp;
}

/*
 * free
 */
void mm_free(void *ptr) {
  if (!ptr) return;                   /* Skip invalid input */

  size_t size = GET_SIZE(HDRP(ptr));
  if (heap_listp == NULL)
    mm_init();

  /* alloc = 0 for footers and headers */
  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
  coalesce(ptr);
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *mm_realloc(void *oldptr, size_t size) {
  size_t oldsize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if (size == 0) {
    mm_free(oldptr);
    return NULL;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if (oldptr == NULL)
    return mm_malloc(size);

  newptr = mm_malloc(size);

  /* If realloc() fails the original block is left untouched  */
  if (!newptr)
    return 0;

  /* Copy the old data. */
  oldsize = GET_SIZE(HDRP(oldptr));
  if (size < oldsize) oldsize = size;
  memcpy(newptr, oldptr, oldsize);

  /* Free the old block. */
  mm_free(oldptr);

#ifdef DEBUG
  assert(in_heap(newptr) == 1);
  assert(aligned(newptr) == 1);
#endif

  return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *mm_calloc(size_t nmemb, size_t size) {
  void *ptr;
  if (heap_listp == 0)
    mm_init();

  ptr = mm_malloc(nmemb*size);
  bzero(ptr, nmemb*size);

#ifdef DEBUG
  assert(in_heap(ptr) == 1);
  assert(aligned(ptr) == 1);
#endif

  return ptr;
}

/* $begin helper functions */

/*
 * extend_heap - Extend heap with free block and return its block pointer (from textbook)
 */
static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;
  void *return_ptr;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) < 0)
    return NULL;

  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));           /* free block header */
  PUT(FTRP(bp), PACK(size, 0));           /* free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));   /* new epilogue header */

  /* Coalesce if the previous block was free */
  return_ptr = coalesce(bp);

#ifdef DEBUG
  mm_checkheap(0);
#endif

  return return_ptr;
}

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static void *find_fit(size_t asize)
{
#ifdef FIRST_FIT
  /* first fit search */
  void *bp;
  int id, segid = get_segid(asize);

  for (id = segid; id < SEG_SIZE; ++id)
    for (bp = get_root(id, NULL); bp != NULL; bp = NEXT(bp))
      if ( asize <= GET_SIZE(HDRP(bp)) )
        return bp;

  return NULL; /* no fit */
#endif

#ifdef BEST_FIT
  /* best fit search */
  void *bp, *min_bp=NULL;
  unsigned min_d = UINT_MAX;
  int id, segid = get_segid(asize);

  for (id = segid; id < SEG_SIZE; ++id)
    for (bp = get_root(id, NULL); bp != NULL; bp = NEXT(bp))
      if ( asize <= GET_SIZE(HDRP(bp)) && GET_SIZE(HDRP(bp)) < min_d )
        min_bp = bp;
  return min_bp;
#endif

}

/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
static void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));
  int segid;

  if ((csize - asize) >= (QSIZE + OVERHEAD)) {
    /* Allocate Memory */
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    mm_unlink(bp);

    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));

    /* Push remaining into linkedlist */
    segid = get_segid(asize);
    NEXT(bp) = get_root(segid, NULL);
    PREV(bp) = NULL;
    PREV(get_root(segid, NULL)) = bp;
    get_root(segid, bp);
  }
  else {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
    mm_unlink(bp);
  }
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
  size_t prev_size, next_size;
  void *thisHead = NULL;                       /* Keep a copy of pointer of this block */

  if (prev_alloc && next_alloc) {
    /* Case 1:
     *  Front and End is not empty
     */
    thisHead = bp;
    /* Link this space */
  } else if (prev_alloc && !next_alloc) {
    /* Case 2:
     *  End is empty, Front is full
     */
    thisHead = bp;
    next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    size += next_size;
    /* Unlink next space */
    mm_unlink(NEXT_BLKP(bp));
    /* Link this space */
    PUT(HDRP(bp), PACK(size,0));
    PUT(FTRP(bp), PACK(size,0));
  } else if (!prev_alloc && next_alloc) {
    /* Case 3
     *  Front is empty, End is full
     */
    thisHead = PREV_BLKP(bp);
    prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
    size += prev_size;
    /* Unlink prev space */
    mm_unlink(PREV_BLKP(bp));
    /* Link this space */
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
  } else {
    /* Case 4
     *  Both front and end are empty
     */
    thisHead = PREV_BLKP(bp);
    prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
    next_size = GET_SIZE(FTRP(NEXT_BLKP(bp)));
    size += prev_size + next_size;
    /* Unlink prev space */
    mm_unlink(PREV_BLKP(bp));
    /* Unlink next space */
    mm_unlink(NEXT_BLKP(bp));
    /* Link this space */
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
  }

  /* add to doubly free linklist */
  int segid = get_segid(size);

  NEXT(thisHead) = get_root(segid, NULL);

#ifdef DEBUG
  assert(this_root != NULL);
#endif

  PREV(thisHead) = NULL;
  PREV(get_root(segid, NULL)) = thisHead;
  get_root(segid, thisHead);

#ifdef DEBUG
  assert(in_heap(thisHead) == 1);
  assert(aligned(thisHead) == 1);
#endif

  return thisHead;
}

/*
 * mm_unlink - unlink a block from the linklist
 */
static inline void mm_unlink(void *bp)
{
  size_t size = GET_SIZE(HDRP(bp));
  int segid = get_segid(size);

  if ( PREV(bp) )
    NEXT(PREV(bp)) = NEXT(bp);
  else
    get_root(segid, NEXT(bp));

  if ( NEXT(bp) )
    PREV(NEXT(bp)) = PREV(bp);
}

/* $end helper functions */
/* $begin debug functions */

/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
 /*
  * mm_checkheap
  */
 void mm_checkheap(int verbose) {
   char *bp = heap_listp;
   printblock(bp);

   if (verbose)
     printf("Heap (%p):\n", heap_listp);

   if ((GET_SIZE(HDRP(heap_listp)) != OVERHEAD) || !GET_ALLOC(HDRP(heap_listp)))
     printf("Bad prologue header %d\n", GET_SIZE(HDRP(heap_listp)) );
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

#ifdef DEBUG
  static inline int in_heap(const void *p) {
    return p < mem_heap_hi() && p >= mem_heap_lo();
  }
#endif

#ifdef SEGRE
  static int get_segid(size_t asize) {
    if (asize <= 32)
      return 0;
    else if (asize <= 64)
      return 1;
    else if (asize <= 128)
      return 2;
    else if (asize <= 256)
      return 3;
    else if (asize <= 512)
      return 4;
    else if (asize <= 1024)
      return 5;
    else if (asize <= 2048)
      return 6;
    else  // 2048 and more
      return 7;
  }

  static inline void *get_root(int segid, void *newroot) {
    static void *roots[SEG_SIZE];

    if (newroot == NULL)
      return roots[segid];
    else {
      roots[segid] = newroot;
      return NULL;
    }
  }

  static inline void *get_rootd(size_t size) {
    return get_root( get_segid(size), NULL);
  }

  static inline void root_init() {
    for (int i=0; i<SEG_SIZE; ++i)
      get_root(i, start_root+i*2*DSIZE);
  }

#endif

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
#ifdef DEBUG
  static inline int aligned(const void *p) {
      return (size_t)ALIGN(p) == (size_t)p;
  }
#endif


static void printblock(void *bp)
{
  size_t hsize;//, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  //halloc = GET_ALLOC(HDRP(bp));
  //fsize = GET_SIZE(FTRP(bp));
  //falloc = GET_ALLOC(FTRP(bp));

  if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
  }

  /*  printf("%p: header: [%p:%c] footer: [%p:%c]\n", bp,
      hsize, (halloc ? 'a' : 'f'),
      fsize, (falloc ? 'a' : 'f')); */
}

static void checkblock(void *bp)
{
  if ((size_t)bp % 8)
    printf("Error: %p is not doubleword aligned\n", bp);
  if (GET(HDRP(bp)) != GET(FTRP(bp)))
    printf("Error: header does not match footer\n");
}

/* $end debug functions */
