/*
 * mm.c
 *
 * Name: [FILL IN]
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 * Also, read malloclab.pdf carefully and in its entirety before beginning.
 *
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <stdbool.h>
#include <stdint.h>

#include "mm.h"
#include "memlib.h"

/*
 * If you want to enable your debugging output and heap checker code,
 * uncomment the following line. Be sure not to have debugging enabled
 * in your final submission.
 */
// #define DEBUG

#ifdef DEBUG
/* When debugging is enabled, the underlying functions get called */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#else
/* When debugging is disabled, no code gets generated */
#define dbg_printf(...)
#define dbg_assert(...)
#endif /* DEBUG */

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* DRIVER */

/* What is the correct alignment? */
#define ALIGNMENT 16

static const size_t WSIZE = 8;             /* word size (bytes) */  
static const size_t DSIZE = 16;            /* 2 words size (bytes) */
static const size_t MIN_BLOCK_SIZE = 32; 


static char* heap_start;

static char* heap_start_ptr;

static size_t heap_visual[5000];

// static char heap_start_ptr[64];
// static char heap_listp[64];


void copy_data() {
    memcpy(heap_visual, heap_start, 1000);
}


/* rounds up to the nearest multiple of ALIGNMENT */
static size_t align(size_t x)
{
    return ALIGNMENT * ((x+ALIGNMENT-1)/ALIGNMENT);
}

static size_t align_2(size_t words) {
    size_t size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    return size;
}


static size_t get_size(void* ptr) {
    // size in terms of bytes
    size_t size = *(size_t*) ptr & ~0xF;
    return size;
}


static void set_word(void* header, size_t size, bool allocated) {
    *(size_t*) header = size | allocated;
    // copy_data();
}

static void* get_header_ptr(void* block_ptr) {
    return (char*) block_ptr - WSIZE;
}

static void* get_footer_ptr(void* block_ptr) {
    void* header_ptr = get_header_ptr(block_ptr);
    size_t size = get_size(header_ptr);
    char* footer_ptr = (char*)block_ptr + size - DSIZE;
    return footer_ptr; 
}

static bool get_allocated(void* ptr) {
    bool allocated = *(size_t*) ptr & 1;
    return allocated;
}


static void* get_next_block_ptr(void* block_ptr) {
    void* header_ptr = get_header_ptr(block_ptr);
    size_t size = get_size(header_ptr);
    char* next_block_ptr = (char*) block_ptr + size;
    return next_block_ptr;
}

static void* get_prev_block_ptr(void* block_ptr) {
    void* prev_footer_ptr = (char*) block_ptr - DSIZE;
    size_t size = get_size(prev_footer_ptr);
    char* prev_block_ptr = (char*) block_ptr - size;
    return prev_block_ptr;
}

void init_test() {
    size_t aligned = align(17);
    size_t aligned_2 = align_2(3);
    printf("align(17):%ld, align_2(17):%ld\n", aligned, aligned_2);
    printf("sizeof(size_t):%ld\n", sizeof(size_t));

    void* heap_lo = mem_heap_lo();
    void* heap_hi = mem_heap_hi();
    size_t heap_size = mem_heapsize();

    printf("heap_lo:%p\n", heap_lo);
    printf("heap_hi:%p\n", heap_hi);
    printf("heap_size:%lu\n", heap_size);

    // heap_listp = mem_sbrk(32);
    heap_start_ptr = mem_sbrk(32);
    printf("heap_start_ptr:%p\n", heap_start_ptr);
    for(int i=0;i<4;i ++) {
        heap_start_ptr[i] = i + 65;
        printf("%c", heap_start_ptr[i]);
    }
    printf("\n");

    heap_lo = mem_heap_lo();
    heap_hi = mem_heap_hi();
    heap_size = mem_heapsize();

    printf("heap_lo:%p\n", heap_lo);
    printf("heap_hi:%p\n", heap_hi);
    printf("heap_size:%lu\n", heap_size);

    // heap_listp = mem_sbrk(32);
    char* heap_start_ptr2 = mem_sbrk(64);
    printf("heap_start_ptr2:%p, size:%ld\n", heap_start_ptr2, ((char*)heap_hi-heap_start_ptr2));

    heap_lo = mem_heap_lo();
    heap_hi = mem_heap_hi();
    heap_size = mem_heapsize();

    printf("heap_start_ptr:%p, size:%ld\n", heap_start_ptr, ((char*)heap_hi-heap_start_ptr));
    for(int i=0;i<4;i ++) {
        printf("%c", heap_start_ptr[i]);
    }
    printf("\n");

    printf("heap_lo:%p\n", heap_lo);
    printf("heap_hi:%p\n", heap_hi);
    printf("heap_size:%lu\n", heap_size);

}

void* extend(size_t aligned_size){

    void* block_ptr = mem_sbrk(aligned_size);
    // mem_memset(block_ptr, 0, aligned_size);
    // copy_data();
    if(block_ptr == NULL){
        return NULL;
    }

    // set newly created block's header and footer
    void* header = get_header_ptr(block_ptr);
    set_word(header, aligned_size, false);
    

    void* footer = get_footer_ptr(block_ptr);
    set_word(footer, aligned_size, false);

    // set the new epilogue header
    void* next_block_ptr = get_next_block_ptr(block_ptr);
    void* next_block_ptr_header = get_header_ptr(next_block_ptr);

    // size_t offset = next_block_ptr_header - block_ptr;

    set_word(next_block_ptr_header, 0, true);

    // TODO: coalesce
    return block_ptr;
}

/*
 * Initialize: returns false on error, true on success.
 */
bool mm_init(void)
{
    // initialize the heap with
    // one initial padding (1 word)
    // one prologue block (2 word)
    // one epilogue block header (1 word)
    int default_heap_size = 4 * WSIZE;
    heap_start_ptr = mem_sbrk(default_heap_size);
    heap_start = heap_start_ptr;
    if (heap_start_ptr == NULL) return false;

    set_word(heap_start_ptr, 0, false);
    set_word(heap_start_ptr + WSIZE * 1, DSIZE, true);
    set_word(heap_start_ptr + WSIZE * 2, DSIZE, true);
    set_word(heap_start_ptr + WSIZE * 3, 0, true);

    heap_start_ptr += WSIZE * 2;

    copy_data();


    void* new_block_ptr = extend(MIN_BLOCK_SIZE);
    if(new_block_ptr == NULL) {
        return false;
    }

    return true;
}


void* find_free_block(size_t aligned_size) {
    void* bp = heap_start_ptr;

    int block_index = 0;
    while (true){
        void* header = get_header_ptr(bp);
        bool allocated = get_allocated(header);
        size_t block_size = get_size(header);
        if(block_size == 0) break;

        // printf("block_index:%d, block_size:%ld, allocated:%d", block_index, block_size, allocated);
        if(!allocated && block_size > aligned_size) {
            // printf(" FOUND empty\n");
            return bp;
        }
        
        // printf(" none empty, continue\n");
        block_index++;
        bp = get_next_block_ptr(bp);
    }

    // printf("cannot find free\n");
    return NULL;
}


void place(void* block_ptr, size_t aligned_size) {
    void* header = get_header_ptr(block_ptr);
    void* footer = get_footer_ptr(block_ptr);

    size_t free_size = get_size(header);

    size_t remain_bytes = free_size - aligned_size;
    if(remain_bytes >= MIN_BLOCK_SIZE) {
        // split this block into two
        set_word(header, aligned_size, true);
        set_word(footer, aligned_size, true);

        block_ptr = get_next_block_ptr(block_ptr);
        
        header = get_header_ptr(block_ptr);
        set_word(header, remain_bytes, false);

        footer = get_footer_ptr(block_ptr);
        set_word(footer, remain_bytes, false);
    } else {
        set_word(header, free_size, true);
        set_word(footer, free_size, true);
    }
}

/*
 * malloc
 */
void* malloc(size_t size)
{
    if(size == 0) {
        return NULL;
    }
    // printf("malloc %ld\n", size);
    size_t aligned_size = align(size + WSIZE);
    aligned_size += DSIZE; // add header and footer size
    void* free_block_ptr = find_free_block(aligned_size);
    if (free_block_ptr != NULL) {
        place(free_block_ptr, aligned_size);
        return free_block_ptr;
    }

    void* new_block_ptr = extend(aligned_size);
    if (new_block_ptr == NULL) {
        return NULL;
    }

    place(new_block_ptr, aligned_size);

    // copy_data();

    return new_block_ptr;
}

/*
 * free
 */
void free(void* ptr)
{
    if (ptr == NULL) return;

    void* header = get_header_ptr(ptr);
    void* footer = get_footer_ptr(ptr);
    size_t size = get_size(header);
    set_word(header, size, false);
    set_word(footer, size, false);
    return;
}

/*
 * realloc
 */
void* realloc(void* oldptr, size_t size)
{
    if (size == 0) {
        free(oldptr);
        return NULL;
    }

    if(oldptr == NULL) {
        return malloc(size);
    }

    void* new_block_ptr = malloc(size);

    if(new_block_ptr == NULL){
        return NULL;
    }

    size_t oldsize = get_size(get_header_ptr(oldptr));
    if(size < oldsize) {
        oldsize = size;
    }

    mem_memcpy(new_block_ptr, oldptr, oldsize);

    free(oldptr);

    return new_block_ptr;
}

/*
 * calloc
 * This function is not tested by mdriver, and has been implemented for you.
 */
void* calloc(size_t nmemb, size_t size)
{
    void* ptr;
    size *= nmemb;
    ptr = malloc(size);
    if (ptr) {
        memset(ptr, 0, size);
    }
    return ptr;
}

/*
 * Returns whether the pointer is in the heap.
 * May be useful for debugging.
 */
static bool in_heap(const void* p)
{
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Returns whether the pointer is aligned.
 * May be useful for debugging.
 */
static bool aligned(const void* p)
{
    size_t ip = (size_t) p;
    return align(ip) == ip;
}

/*
 * mm_checkheap
 */
bool mm_checkheap(int lineno)
{
#ifdef DEBUG
    
#endif /* DEBUG */
    return true;
}
